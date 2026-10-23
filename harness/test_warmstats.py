import unittest

from warmstats import distribution, summarize, timelines


class WarmStatsTests(unittest.TestCase):
    def edits(self, label="; program=unit"):
        return [dict(wall_seconds=i, exit_code=0,
                     log=f"timeline-us: roots={i * 1000} check=100{label}\n")
                for i in range(1, 6)]

    def test_five_samples(self):
        result = summarize(self.edits())
        self.assertEqual(result["wall_seconds"], dict(median=3, min=1, max=5))
        self.assertEqual(result["program_phase_seconds"]["unit"]["roots"],
                         dict(median=.003, min=.001, max=.005))

    def test_unlabeled_old_binary(self):
        result = summarize(self.edits(""))
        self.assertIsNone(result["program_phase_seconds"])
        self.assertEqual(result["longest_program_phase_seconds"]["roots"]["median"], .003)

    def test_overlapping_programs(self):
        edits = self.edits()
        for edit in edits:
            edit["log"] += "timeline-us: roots=9000 check=200; program=other\n"
        self.assertEqual(summarize(edits)["longest_program_phase_seconds"]["roots"]["median"], .009)

    def test_empty_and_failed(self):
        self.assertEqual(timelines(""), [])
        with self.assertRaises(AssertionError):
            summarize([])
        with self.assertRaises(AssertionError):
            summarize([dict(wall_seconds=1, exit_code=1, log="")] * 5)
        with self.assertRaises(AssertionError):
            summarize([dict(wall_seconds=1, exit_code=0, log="")] * 5)


if __name__ == "__main__":
    unittest.main()
