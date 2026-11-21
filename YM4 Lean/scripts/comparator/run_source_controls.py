"""Run thirteen data-only controls against the source-statement adapter.

The adapter is not a proof checker. In particular, two valid proof terms for
the same theorem type are intentionally accepted.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def main():
    binary = HERE / '.lake/build/bin' / ('compare_source_statements.exe' if os.name == 'nt' else 'compare_source_statements')
    if not binary.is_file():
        raise SystemExit('Build with lake build compare_source_statements first.')
    cases = []
    for directory, expected in [('controls', 10), ('source-controls', 3)]:
        rows = json.loads((HERE/directory/'manifest.json').read_text(encoding='utf-8'))['cases']
        if len(rows) != expected:
            raise SystemExit('Unexpected control manifest size: ' + directory)
        cases.extend((directory, row) for row in rows)
    receipt = {'status': 'running', 'binarySha256': sha(binary),
               'adapterSha256': sha(HERE/'CompareSourceStatements.lean'),
               'supportSha256': sha(HERE/'SerializedSupport.lean'),
               'fullProjectCompared': False, 'kernelProofCheckPerformed': False, 'cases': []}
    for directory, case in cases:
        folder = HERE/directory/case['name']
        for name, digest in case['files'].items():
            if sha(folder/name) != digest:
                raise SystemExit('Control digest mismatch: ' + case['name'] + '/' + name)
        result = subprocess.run([str(binary), str(folder/'challenge.ndjson'),
                                 str(folder/'solution.ndjson'), str(folder/'scope.json')],
                                capture_output=True, timeout=120)
        output = (result.stdout + result.stderr).decode('utf-8', errors='replace')
        marker = 'source statement comparison passed:' if case['accept'] else case['marker']
        passed = result.returncode == (0 if case['accept'] else 1) and marker in output
        receipt['cases'].append({'name': case['name'], 'passed': passed,
                                 'exitCode': result.returncode, 'output': output})
        print(case['name'] + ': ' + ('passed' if passed else 'FAILED'))
    receipt['status'] = 'passed' if all(row['passed'] for row in receipt['cases']) else 'failed'
    output = HERE/'controls-runs'/('source-' + str(time.time_ns()) + '.json')
    output.parent.mkdir(exist_ok=True)
    with output.open('x', encoding='utf-8') as f:
        json.dump(receipt, f, indent=2); f.write('\n')
    print('Receipt: ' + str(output))
    raise SystemExit(0 if receipt['status'] == 'passed' else 1)

if __name__ == '__main__':
    main()
