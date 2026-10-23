import unittest

from bench import daemon_steps


class DaemonStepsTests(unittest.TestCase):
    def test_program_labels(self):
        text = ("timeline-us: notice=1000 apply=200 roots=300 link=4; program=unit\n"
                "timeline-us: notice=2000 apply=400 roots=500 link=6; program=other\n")
        self.assertEqual(daemon_steps(text), dict(apply=.6, roots=.8, link=.01))

    def test_unlabeled(self):
        self.assertEqual(daemon_steps("timeline-us: notice=1000 apply=200 roots=300\n"),
                         dict(apply=.2, roots=.3))

    def test_empty(self):
        self.assertEqual(daemon_steps(""), {})

    def test_invalid_timing(self):
        with self.assertRaises(ValueError):
            daemon_steps("timeline-us: roots=invalid; program=unit\n")


if __name__ == "__main__":
    unittest.main()
