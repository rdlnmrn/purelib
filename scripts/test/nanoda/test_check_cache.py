#!/usr/bin/env python3
"""Exercise checker-cache invalidation, corruption, failure and concurrency."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import tempfile

from scripts.paths import ROOT
from scripts.nanoda import check_stream as m


def main():
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        cache, checker, stream, config, counter = [directory / n for n in
                                                   ['cache', 'checker', 'stream', 'config', 'counter']]
        config.write_bytes((ROOT / 'scripts/nanoda/config.json').read_bytes())
        stream.write_bytes(b'good stream')
        checker.write_text('''#!/usr/bin/env python3
import sys
from pathlib import Path
counter = Path(''' + repr(str(counter)) + ''')
counter.write_text(str(int(counter.read_text()) + 1 if counter.exists() else 1))
data = sys.stdin.buffer.read()
if data.startswith(b'fail'):
    print('checker failed')
    sys.exit(1)
if data.startswith(b'skip'):
    print('skipping exported axiom bad')
if data.startswith(b'axiom'):
    print('axiom ' + data.decode().split()[1] + ' : fake')
print('Checked 17 declarations with no errors')
''')
        checker.chmod(0o755)
        first, hit = m.check(stream, checker, config, cache)
        assert first['declarations'] == 17 and not hit
        assert m.check(stream, checker, config, cache) == (first, True)
        assert counter.read_text() == '1'
        receipt = next(cache.glob('*.json'))
        old = json.loads(receipt.read_text())
        old['identity']['policy'] = 'nanoda-only-propext-no-skips-v1'
        old['result']['axioms'] = ['propext']
        old['result']['report'] = 'axiom propext : fake\nChecked 17 declarations with no errors\n'
        old_key = hashlib.sha256(json.dumps(old['identity'], sort_keys=True).encode()).hexdigest()
        receipt.unlink()
        old_receipt = cache / (old_key + '.json')
        old_receipt.write_text(json.dumps(old))
        assert not m.check(stream, checker, config, cache)[1]
        assert counter.read_text() == '2', 'old permitted-propext receipt reused'
        assert json.loads(old_receipt.read_text()) == old
        stream.write_bytes(b'Good stream')  # same byte length must still invalidate
        assert not m.check(stream, checker, config, cache)[1]
        checker.write_text(checker.read_text() + '# new checker revision\n')
        assert not m.check(stream, checker, config, cache)[1]
        settings = json.loads(config.read_text()); settings['num_threads'] = 2
        config.write_text(json.dumps(settings))
        assert not m.check(stream, checker, config, cache)[1]
        assert counter.read_text() == '5'
        before = set(cache.glob('*.json'))
        for payload in [b'fail', b'skip', b'axiom propext', b'axiom Classical.choice',
                        b'axiom Quot.sound', b'axiom other']:
            stream.write_bytes(payload)
            try:
                m.check(stream, checker, config, cache)
            except (ValueError, RuntimeError):
                pass
            else:
                raise AssertionError('failed or incomplete check was cached')
            assert set(cache.glob('*.json')) == before
        safe_settings = config.read_text()
        for field, value in [('permitted_axioms', ['propext']),
                             ('unpermitted_axiom_hard_error', False),
                             ('unsafe_permit_all_axioms', True),
                             ('use_stdin', False), ('print_axioms', False),
                             ('print_success_message', False)]:
            settings = json.loads(safe_settings)
            settings[field] = value
            config.write_text(json.dumps(settings))
            calls = counter.read_text()
            try:
                m.check(stream, checker, config, cache)
            except ValueError as error:
                assert field in str(error)
            else:
                raise AssertionError('unsafe checking configuration accepted')
            assert counter.read_text() == calls
            assert set(cache.glob('*.json')) == before
        config.write_text(safe_settings)
        for report in ['', 'Checked 0 declarations with no errors\n',
                       'Checked 1 declarations with no errors\n' * 2,
                       'skipping exported proof\nChecked 1 declarations with no errors\n']:
            try:
                m.result(report)
            except ValueError:
                pass
            else:
                raise AssertionError('incomplete checker report accepted')
        stream.write_bytes(b'concurrent')
        calls = int(counter.read_text())
        with ThreadPoolExecutor(max_workers=2) as workers:
            results = list(workers.map(lambda _: m.check(stream, checker, config, cache), range(2)))
        assert sorted(hit for _, hit in results) == [False, True]
        assert int(counter.read_text()) == calls + 1
        receipt = (set(cache.glob('*.json')) - before).pop()
        saved = json.loads(receipt.read_text())
        saved['result']['report'] = 'Checked 18 declarations with no errors\n'
        receipt.write_text(json.dumps(saved))
        try:
            m.check(stream, checker, config, cache)
        except ValueError as error:
            assert 'inconsistent' in str(error)
        else:
            raise AssertionError('corrupted receipt accepted')
        # An absent receipt triggers a real check, rather than trusting logs.
        receipt.unlink()
        assert not m.check(stream, checker, config, cache)[1]
    actual = ROOT / '.lake/nanoda-experiments/control-v1/native.0.ndjson'
    if actual.exists():
        checker = Path(os.environ.get('NANODA_BIN',
            str(ROOT / '.external/nanoda/target/release/nanoda_bin')))
        config = ROOT / 'scripts/nanoda/config.json'
        cache = ROOT / '.lake/nanoda-checked'
        # Historical positive receipts used a policy permitting propext. The
        # original stream stays unchanged; its declared axioms now require real
        # checker rejection, not inheritance of the old successful receipt.
        declares_axiom = any('axiom' in json.loads(line)
                             for line in actual.read_text().splitlines())
        if declares_axiom:
            before = set(cache.glob('*.json')) if cache.exists() else set()
            try:
                m.check(actual, checker, config, cache)
            except RuntimeError as error:
                assert 'unpermitted axiom' in str(error)
            else:
                raise AssertionError('historical axiom-bearing stream accepted')
            assert set(cache.glob('*.json')) == before
        else:
            checked, _ = m.check(actual, checker, config, cache)
            assert checked['declarations'] == 284
            assert m.check(actual, checker, config, cache) == (checked, True)
    print('nanoda checker-cache regression passed')


if __name__ == '__main__':
    main()
