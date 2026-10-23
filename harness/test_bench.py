import ast
from pathlib import Path
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

    def test_inline_timeline_consumers(self):
        for name in ("scaling.py", "dxedits.py"):
            tree = ast.parse(Path(__file__).with_name(name).read_text())
            assignment = next(node for node in ast.walk(tree)
                              if isinstance(node, ast.Assign) and any(
                                  isinstance(target, ast.Name) and target.id == "steps"
                                  for target in node.targets))
            expression = compile(ast.Expression(assignment.value), name, "eval")
            for suffix in ("", "; program=unit"):
                with self.subTest(name=name, suffix=suffix):
                    self.assertEqual(eval(expression, {"b": [""] * 7 + ["roots=200" + suffix]}),
                                     dict(roots=.2))
            self.assertEqual(eval(expression, {"b": [""] * 8}), {})
            with self.assertRaises(ValueError):
                eval(expression, {"b": [""] * 7 + ["roots=invalid; program=unit"]})


if __name__ == "__main__":
    unittest.main()
