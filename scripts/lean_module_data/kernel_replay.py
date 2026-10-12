"""Original ordered checked replay plan; all environment decisions are native."""
from functools import cmp_to_key
from .observations import Observations,name_observer,quick_cmp
from .render import Renderer

def text(ref):
    return Renderer(ref.d).name_string(ref.name)

def unsafe(ref):
    if ref.kind==1:return ref.scalar[0] in (0,2)
    if ref.kind in (0,3,6):return ref.scalar[0]!=0
    if ref.kind in (5,7):return ref.scalar[1]!=0
    return False

def replay(old,writer):
    """Preserve original pending/group/quot ordering with explicit finite tasks."""
    entries=old.entries(True)
    refs={name_observer(r.d,r.name):(i,r) for i,(_,r,_) in enumerate(entries)}
    remaining={k for k,(_,r) in refs.items() if not unsafe(r)}
    pending=set();ctors=set();recursors=set();actions=[];groups=[];quotients=[]
    obs=Observations.__new__(Observations)
    def ordered(keys):return sorted(keys,key=cmp_to_key(quick_cmp))
    def list_names(r,ptr):
        idx=r.d.decode('List:Name',ptr)
        return [name_observer(r.d,i) for i in r.d.list_items(idx)]
    tasks=[('enter',k) for k in reversed(ordered(remaining))]
    while tasks:
        op,k=tasks.pop()
        if op=='enter':
            if k not in remaining:continue
            remaining.remove(k);pending.add(k);r=refs[k][1]
            tasks.append(('finish',k))
            tasks.extend(('enter',dep) for dep in reversed(ordered(obs.used(r))))
            continue
        i,r=refs[k]
        if op=='finish':
            if k not in pending:continue
            if r.kind<=3:actions.append(('O',i,text(r)))
            elif r.kind==5:
                all_=list_names(r,r.fields[3])
                for n in all_:remaining.discard(n);pending.discard(n)
                tasks.append(('group',k))
                dependencies=[]
                for n in all_:
                    member=refs[n][1]
                    for cn in list_names(member,member.fields[4]):
                        dependencies.extend(ordered(obs.used(refs[cn][1])))
                tasks.extend(('enter',dep) for dep in reversed(dependencies))
                continue
            elif r.kind==6:ctors.add(k)
            elif r.kind==7:recursors.add(k)
            elif r.kind==4:
                tasks.append(('quot',k))
                eq=next((n for n,(_,v) in refs.items() if text(v)=='Eq'),None)
                if eq is not None:tasks.append(('enter',eq))
                continue
            else:raise ValueError('unsupported original declaration kind')
        elif op=='group':
            infos=[]
            for n in list_names(r,r.fields[3]):
                member=refs[n][1]
                cs=[refs[c][1] for c in list_names(member,member.fields[4])]
                ctor_values=[writer.ctor(0,[writer.clone(c.d.parts,c.base[0]),writer.clone(c.d.parts,c.base[2])]) for c in cs]
                infos.append(writer.ctor(0,[writer.clone(member.d.parts,member.base[0]),writer.clone(member.d.parts,member.base[2]),writer.list(ctor_values)]))
            g=writer.ctor(0,[writer.clone(r.d.parts,r.base[1]),writer.ctor(0,[writer.clone(r.d.parts,r.fields[1]),writer.list(infos)])])
            groups.append(g);actions.append(('G',len(groups)-1,text(r)))
        elif op=='quot':
            quotients.append(9);actions.append(('Q',len(quotients)-1,text(r)))
        pending.discard(k)
    for k in ordered(ctors):actions.append(('C',refs[k][0],text(refs[k][1])))
    for k in ordered(recursors):actions.append(('R',refs[k][0],text(refs[k][1])))
    return actions,groups,quotients
