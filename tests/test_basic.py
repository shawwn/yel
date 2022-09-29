import unittest

from yel import bel

class TestCase(unittest.TestCase):
    def test_basic(self):
        self.assertEqual(1, 1)
    def test_bel(self):
        test = self.assertEqual
        test(1, bel.bel(1))
        test(1, bel.bel(["let", "x", 1, "x"]))
        x = 1
        test(1, bel.bel("x", bel.unset, [locals()]))

if __name__ == '__main__':
    unittest.main()
