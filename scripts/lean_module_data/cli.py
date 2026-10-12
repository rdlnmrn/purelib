#!/usr/bin/env python3
"""Read pinned compiled imports or declaration contracts using checked host bytes."""
import argparse
import sys
from pathlib import Path
from scripts.lean_module_data.compact import inventory
from scripts.lean_module_data.contracts import capture, dumps
from scripts.lean_module_data.paths import find_olean, search_path, render_name
from scripts.lean_module_data.schema1 import records as schema1_records, diagnostic as schema1_diagnostic
from scripts.lean_module_data.observations import Observations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest='mode', required=True)
    kernel = modes.add_parser('type-equivalence', help='official checked-kernel replay of old constants at complete new types')
    kernel.add_argument('old', nargs='?', type=Path); kernel.add_argument('new', nargs='?', type=Path)
    kernel.add_argument('names', nargs='*')
    kernel.add_argument('--toolchain', type=Path)
    kernel.add_argument('--kernel-cache', type=Path)
    kernel.add_argument('--receipt', type=Path)
    inputs = modes.add_parser('inputs')
    inputs.add_argument('manifest', type=Path); inputs.add_argument('output', type=Path)
    contracts = modes.add_parser('contracts')
    contracts.add_argument('modules', nargs='+')
    contracts.add_argument('--schema', type=int, choices=(1, 2), default=2)
    dependencies = modes.add_parser('dependencies', help='compiled dependency owners and persisted namespace registrations')
    dependencies.add_argument('module'); dependencies.add_argument('namespaces', nargs='*')
    trace = modes.add_parser('trace', help='compiled shortest paths or exact application Expr Repr')
    trace.add_argument('--mode', dest='trace_mode', choices=('axiom','use'), default='axiom')
    trace.add_argument('--target', default='Quot.sound')
    trace.add_argument('module'); trace.add_argument('declarations', nargs='+')
    audit_keys = modes.add_parser('audit-input-keys', help='original metadata keys plus consumed interpreter closure')
    audit_keys.add_argument('inventory', type=Path); audit_keys.add_argument('metadata_keys', type=Path)
    audit_support = modes.add_parser('audit-support', help='original authoritative support inventory')
    axiom_audit = modes.add_parser('audit', help='authoritative project axiom backend')
    axiom_audit.add_argument('--project', type=Path, required=True)
    axiom_audit.add_argument('--assigned', type=Path, required=True)
    axiom_audit.add_argument('--canonical', choices=('true','false'), required=True)
    axiom_audit.add_argument('--result', type=Path, required=True)
    axiom_audit.add_argument('--all-helpers', action='store_true',
                             help='select every retained kernel helper as an independent project root')
    axiom_audit.add_argument('--report-ir-only', action='store_true',
                             help='write a diagnostic inventory of code without kernel declarations; not an axiom check')
    axiom_audit.add_argument('--imports', type=Path, help='retained actual worker imports, when different from assigned owners')
    modes.add_parser('regression-root', help='required independently audited regression owner')
    for mode in (inputs, contracts, dependencies, trace, axiom_audit, audit_keys, kernel):
        mode.add_argument('--search-path', action='append', type=Path)
    args = parser.parse_args()
    if args.mode == 'regression-root':
        from scripts.lean_module_data.audit import REGRESSION_MODULE
        print(REGRESSION_MODULE)
        return
    if args.mode == 'audit-support':
        from scripts.lean_module_data.audit import SUPPORT
        print('\n'.join(sorted({m for m in SUPPORT if not m.startswith('Lean.')})))
        return
    if args.mode=='type-equivalence' and args.toolchain is not None and args.search_path is None:
        import os
        search=[Path(p) for p in os.environ.get('LEAN_PATH','').split(os.pathsep) if p]+[args.toolchain/'lib/lean']
    else:
        search = args.search_path if args.search_path is not None else search_path()
    if args.mode == 'type-equivalence':
        import os,uuid
        from scripts.lean_module_data.kernel import compare,native_build,Bindings,KernelError
        from scripts.lean_module_data.compact import InvalidArtifact
        try:
            if args.old is None or args.new is None:raise KernelError('usage: OLD_OLEAN NEW_OLEAN NAME...')
            if not args.names:raise KernelError('at least one name is required')
            toolchain=args.toolchain or search[-1].parent.parent
            cache=args.kernel_cache or Path(os.environ.get('XDG_CACHE_HOME',str(Path.home()/'.cache')))/'lean-checked-type-equivalence'
            bindings=Bindings();bindings.add(Path(__file__),'host-driver-source')
            binary=native_build(toolchain,cache,bindings)
            receipt=args.receipt or cache/'invocations'/(uuid.uuid4().hex+'.json')
            receipt.parent.mkdir(parents=True,exist_ok=True)
            env=os.environ.copy()
            if args.search_path is not None:env['LEAN_PATH']=os.pathsep.join(str(p) for p in search)
            compare(args.old,args.new,args.names,binary,toolchain,search,receipt,env,bindings)
        except (KernelError,InvalidArtifact,OSError) as error:
            sys.stderr.buffer.write(('uncaught exception: '+str(error)+'\n').encode('utf8'));sys.stderr.buffer.flush();raise SystemExit(1)
    elif args.mode == 'audit-input-keys':
        from scripts.lean_module_data.audit import input_keys
        sys.stdout.write(input_keys(args.inventory,args.metadata_keys,search))
    elif args.mode == 'audit':
        from scripts.lean_module_data.audit import audit
        def names(path):
            rows=[line.strip() for line in path.read_text().splitlines() if line.strip()]
            if not rows or len(set(rows)) != len(rows) or any(not __import__('scripts.lean_module_data.paths',fromlist=['parse_name']).parse_name(n) for n in rows):
                raise ValueError('empty, duplicate or invalid audit module manifest: '+str(path))
            return rows
        # Canonical-only planned worker deliberately has no assigned project roots.
        assigned=[line.strip() for line in args.assigned.read_text().splitlines() if line.strip()]
        if len(set(assigned)) != len(assigned) or any(not __import__('scripts.lean_module_data.paths',fromlist=['parse_name']).parse_name(n) for n in assigned): raise ValueError('duplicate or invalid assigned audit module')
        try:
            print(audit(names(args.project), assigned, args.canonical=='true', args.result, search,
                        report_ir_only=args.report_ir_only, imports=names(args.imports) if args.imports else None,
                        all_helpers=args.all_helpers))
        except ValueError as error:
            print('error: '+str(error))
            raise SystemExit(1)
    elif args.mode == 'inputs':
        contents = args.manifest.read_bytes().decode('utf8', 'strict')
        roots = [line.strip(' \t\r\n') for line in contents.split('\n') if line.strip(' \t\r\n')]
        result, _ = inventory(roots, search)
        pending = Path(str(args.output) + '.partial')
        pending.write_text(dumps(result) + '\n', encoding='utf8', newline='\n')
        pending.replace(args.output)
    elif args.mode == 'dependencies':
        try:
            print(dumps(Observations(args.module, search).dependencies(args.namespaces)))
        except (ValueError, OSError) as error:
            if isinstance(error, FileNotFoundError) and error.filename is not None and str(error.filename).endswith('.olean'):
                path = Path(error.filename)
                module = None
                for root in search:
                    try:
                        parts = path.relative_to(root).with_suffix('').parts
                    except ValueError:
                        continue
                    module = render_name(tuple((1, p) for p in parts)); break
                if module is not None:
                    print(f"uncaught exception: object file '{path}' of module {module} does not exist",file=sys.stderr)
                else:
                    print(schema1_diagnostic(error),file=sys.stderr)
            else:
                print(schema1_diagnostic(error),file=sys.stderr)
            raise SystemExit(1)
    elif args.mode == 'trace':
        observation = Observations(args.module, search, trace_environment=True)
        failed = False
        for declaration in args.declarations:
            try:
                for line in observation.trace(args.trace_mode,args.target,declaration): print(line)
            except ValueError as error:
                print('error: '+str(error)); failed = True
        if failed: raise SystemExit(1)
    elif args.schema == 1:
        try:
            for record in schema1_records(args.modules, search):
                sys.stdout.write(dumps(record) + '\n')
        except (ValueError, OSError) as error:
            print(schema1_diagnostic(error), file=sys.stderr)
            raise SystemExit(1)
    else:
        for module in args.modules:
            schema, private, public = capture(module, find_olean(module, search))
            for record in schema.records(module, private, public):
                sys.stdout.write(dumps(record) + '\n')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
