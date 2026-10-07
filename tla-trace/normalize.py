#!/usr/bin/env python3
"""Validate v2 framing, materialize field diffs, and output exporter v1 NDJSON.

An unmatched begin is a divergence, including when later calls completed after
catch_unwind. Never feed a v2 log directly to an older trace spec/tlc_conform.
"""
import argparse
import json
import sys


class Divergence(ValueError):
    pass


def normalize(lines):
    rows = [json.loads(line) for line in lines if line.strip()]
    if not rows or not isinstance(rows[0], dict):
        raise ValueError("missing header")
    header = dict(rows[0])
    version = header.pop("format", None)
    if version not in (None, "tla-trace-v2"):
        raise ValueError(f"unknown format {version!r}")
    state = header.get("state", {})
    output = [header]
    pending = None
    last_id = 0
    pending_index = None
    for line, row in enumerate(rows[1:], 2):
        if not isinstance(row, dict):
            raise ValueError(f"line {line}: expected a record")
        if "begin" in row:
            if version is None or set(row) != {"begin", "step", "params"}:
                raise ValueError(f"line {line}: invalid begin")
            if pending is not None:
                raise Divergence(f"step {pending_index}: unfinished begin {pending['step']}")
            if type(row['begin']) is not int or row['begin'] <= last_id:
                raise ValueError(f"line {line}: nonmonotonic begin id")
            last_id = row['begin']
            pending = row
            pending_index = len(output)
        elif "end" in row:
            if set(row) != {"end"} or type(row["end"]) is not int or pending is None or row['end'] != pending['begin']:
                raise ValueError(f"line {line}: unmatched end")
            pending = None
        else:
            if "diff" in row:
                if version is None or set(row) != {"step", "params", "diff", "remove"}:
                    raise ValueError(f"line {line}: invalid diff")
                if not isinstance(state, dict) or not isinstance(row['diff'], dict):
                    raise ValueError(f"line {line}: diff requires record states")
                if not isinstance(row["remove"], list) or not all(isinstance(k, str) for k in row["remove"]):
                    raise ValueError(f"line {line}: remove must be an array of field names")
                state = dict(state)
                for key in row['remove']:
                    if key not in state or key in row['diff']:
                        raise ValueError(f"line {line}: invalid removed field {key!r}")
                    del state[key]
                state.update(row['diff'])
                row = {"step": row['step'], "params": row['params'], "state": state}
            else:
                if set(row) != {"step", "params", "state"}:
                    raise ValueError(f"line {line}: invalid step fields")
                state = row['state']
            if not isinstance(row['step'], str) or not isinstance(row['params'], dict):
                raise ValueError(f"line {line}: invalid step or params")
            output.append(row)
    if pending is not None:
        raise Divergence(f"step {pending_index}: unfinished begin {pending['step']}")
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input')
    parser.add_argument('output')
    args = parser.parse_args()
    try:
        with open(args.input) as src:
            rows = normalize(src)
        with open(args.output, 'w') as dst:
            for row in rows:
                dst.write(json.dumps(row) + '\n')
    except (ValueError, OSError) as error:
        print(f'trace divergence/format error: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
