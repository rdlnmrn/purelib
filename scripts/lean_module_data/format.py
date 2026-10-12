"""Private direct port of pinned Std.Format's pure string observer.

All work lists are explicit: no recursion limit/depth cap or compiler callback.
Format tags have the original pure observer's no-op behavior.
"""
from collections import deque

NIL = ('nil',)
LINE = ('line',)

def text(value):
    return ('text', value)

def append(left, right):
    return ('append', left, right)

def join(values, separator):
    values = iter(values)
    result = next(values, NIL)
    for value in values:
        result = append(append(result, separator), value)
    return result

def bracket(left, value, right, fill=False):
    return ('group', ('nest', len(left), append(append(text(left), value), text(right))), fill)

def decimal(value):
    """Exact decimal, without Python's configurable large-int conversion cap."""
    if value < 0:
        return '-' + decimal(-value)
    chunks = []
    while value >= 1000000000:
        value, remainder = divmod(value, 1000000000)
        chunks.append(f'{remainder:09d}')
    return str(value) + ''.join(reversed(chunks))

def quote(value):
    """Pinned Char.quoteCore/String.quote grammar, including two-digit control escapes."""
    escaped=[]
    for char in value:
        if char == '\n': escaped.append('\\n')
        elif char == '\t': escaped.append('\\t')
        elif char == '\\': escaped.append('\\\\')
        elif char == '"': escaped.append('\\"')
        elif ord(char) <= 31 or ord(char) == 127: escaped.append('\\x'+f'{ord(char):02x}')
        else: escaped.append(char)
    return '"'+''.join(escaped)+'"'

def space_format(fmt, flatten, margin, width):
    """Pinned spaceUptoLine; explicit continuations preserve lazy merge stopping."""
    tasks=[('eval',fmt,flatten,margin,width)]
    values=[]
    while tasks:
        task=tasks.pop()
        if task[0]=='merge_first':
            _,right,flat,mar,w=task
            first=values.pop()
            if first[2]>w or first[0]:
                values.append(first)
            else:
                tasks.append(('merge_last',first[2]))
                tasks.append(('eval',right,flat,mar,w-first[2]))
        elif task[0]=='merge_last':
            last=values.pop(); values.append((last[0],last[1],task[1]+last[2]))
        else:
            _,f,flat,mar,w=task
            tag=f[0]
            if tag=='nil': values.append((False,False,0))
            elif tag=='line': values.append((not flat,False,1 if flat else 0))
            elif tag=='align':
                if flat and not f[1]: values.append((False,False,0))
                elif w<mar: values.append((False,False,max(mar-w,0)))
                else: values.append((True,False,0))
            elif tag=='text':
                before,separator,_=f[1].partition('\n')
                values.append((bool(separator),bool(flat and separator),len(before)))
            elif tag=='append':
                tasks.append(('merge_first',f[2],flat,mar,w))
                tasks.append(('eval',f[1],flat,mar,w))
            elif tag=='nest': tasks.append(('eval',f[2],flat,mar-f[1],w))
            elif tag=='group': tasks.append(('eval',f[1],True,mar,w))
            elif tag=='tag': tasks.append(('eval',f[2],flat,mar,w))
            else: raise ValueError(f'unknown Format alternative: {tag}')
    assert len(values)==1
    return values[0]

def space_groups(groups, column, width):
    total=0
    for group in groups:
        for fmt,indent in group['items']:
            remaining=max(width-total,0)
            result=space_format(fmt,group['fits'] is True,remaining+column-indent,remaining)
            total+=result[2]
            if result[2]>remaining or result[0]:
                return result[0],result[1],total
    return False,False,total

def push_group(fill, items, remainder, width, column):
    candidate={'fits':not fill,'fill':fill,'items':deque(items)}
    available=max(width-column,0)
    first=space_groups([candidate],column,available)
    if first[2]>available or first[0]:
        combined=first
    else:
        last=space_groups(remainder,column,available-first[2])
        combined=last[0],last[1],first[2]+last[2]
    candidate['fits']=not first[1] and combined[2]<=available
    return candidate

def pretty(fmt, width=120, indent=0, column=0):
    if width<0 or indent<0 or column<0:
        raise ValueError('pretty width/indent/column must be natural')
    groups=deque([{'fits':None,'fill':False,'items':deque([(fmt,indent)])}])
    output=[]
    def emit(value):
        nonlocal column
        output.append(value); column+=len(value)
    def newline(amount):
        nonlocal column
        amount=max(amount,0); output.append('\n'+' '*amount); column=amount
    while groups:
        group=groups[0]
        if not group['items']:
            groups.popleft(); continue
        f,level=group['items'].popleft()
        tag=f[0]
        if tag=='nil': continue
        if tag=='tag': group['items'].appendleft((f[2],level))
        elif tag=='append':
            group['items'].appendleft((f[2],level)); group['items'].appendleft((f[1],level))
        elif tag=='nest': group['items'].appendleft((f[2],level+f[1]))
        elif tag=='text':
            before,separator,after=f[1].partition('\n'); emit(before)
            if separator:
                newline(level); group['items'].appendleft((text(after),level))
                if group['fits'] is not None:
                    remaining=groups.popleft()
                    groups.appendleft(push_group(remaining['fill'],remaining['items'],groups,width,column))
        elif tag=='line':
            if not group['fill']:
                if group['fits'] is True: emit(' ')
                else: newline(level)
            else:
                old=groups.popleft()
                if old['fits'] is True:
                    candidate=push_group(True,old['items'],groups,max(width-1,0),column)
                    if candidate['fits']:
                        emit(' '); groups.appendleft(candidate); continue
                newline(level)
                groups.appendleft(push_group(True,old['items'],groups,width,column))
        elif tag=='align':
            if group['fits'] is True and not f[1]: continue
            if column<level: emit(' '*(level-column))
            else: newline(level)
        elif tag=='group':
            if group['fits'] is True: group['items'].appendleft((f[1],level))
            else: groups.appendleft(push_group(f[2],[(f[1],level)],groups,width,column))
        else: raise ValueError(f'unknown Format alternative: {tag}')
    return ''.join(output)
