import json
import unittest
from normalize import normalize, Divergence

HEADER = {'format': 'tla-trace-v2', 'module': 'M', 'state': {'x': 0, 'ghost': 1}}
BEGIN = {'begin': 1, 'step': 't_add', 'params': {'amount': 1}}
STEP = {'step': 't_add', 'params': {'amount': 1}, 'state': {'x': 1}}

def read(*rows):
    return normalize(map(json.dumps, rows))

class Normalization(unittest.TestCase):
    def test_full_and_legacy(self):
        result = read(HEADER, BEGIN, STEP, {'end': 1})
        self.assertNotIn('format', result[0])
        self.assertEqual(result[1], STEP)
        self.assertEqual(read(*result), result)

    def test_optional_legacy_fields_are_preserved(self):
        header = {'module': 'M'}
        for row in ({'step': 't_add'}, {'step': 't_add', 'params': {}},
                    {'step': 't_add', 'state': {'x': 1}}):
            with self.subTest(row=row):
                self.assertEqual(read(header, row), [header, row])

    def test_omitted_state_clears_diff_base(self):
        result = read(HEADER, {'step': 't_hide'},
            {'step': 't_add', 'params': {}, 'diff': {'x': 2}, 'remove': []})
        self.assertEqual(result[-1]['state'], {'x': 2})

    def test_diff_reconstructs_unchanged_fields_and_removals(self):
        result = read(HEADER, BEGIN,
            {'step': 't_add', 'params': {}, 'diff': {'x': 1}, 'remove': []},
            {'step': 't_hide', 'params': {}, 'diff': {}, 'remove': ['ghost']},
            {'end': 1})
        self.assertEqual(result[1]['state'], {'x': 1, 'ghost': 1})
        self.assertEqual(result[2]['state'], {'x': 1})

    def test_panic_and_caught_panic_are_divergences(self):
        for tail in ([], [STEP], [{'begin': 2, 'step': 't_later', 'params': {}}]):
            with self.assertRaisesRegex(Divergence, 'step 1: unfinished begin t_add'):
                read(HEADER, BEGIN, *tail)

    def test_empty_compound_call(self):
        self.assertEqual(len(read(HEADER, BEGIN, {'end': 1})), 1)

    def test_bad_framing_and_unknown_fields_fail(self):
        bad = [
            [HEADER, {'end': 1}],
            [HEADER, BEGIN, {'end': 2}],
            [HEADER, BEGIN, {'end': True}],
            [HEADER, BEGIN, {'end': 1}, BEGIN],
            [HEADER, dict(STEP, typo={})],
            [HEADER, {'params': {}, 'state': {}}],
            [HEADER, {'step': 't_add', 'params': None}],
            [HEADER, {'step': 't_add', 'prams': {}}],
            [dict(HEADER, format='future')],
            [HEADER, {'step': 't_add', 'params': {}, 'diff': {}, 'remove': ['absent']}],
        ]
        for rows in bad:
            with self.assertRaises(ValueError):
                read(*rows)

if __name__ == '__main__':
    unittest.main()
