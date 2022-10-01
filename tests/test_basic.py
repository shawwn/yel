import unittest

from yel import bel

def do(local, e):
    g = bel.bel("globe")
    return bel.bel(e, g, [local])

class TestCase(unittest.TestCase):
    def test_bel(self):
        test = self.assertEqual
        test(1, do(locals(), 1))
        test(1, do(locals(), ["let", "x", 1, "x"]))
        x = 1
        test(1, do(locals(), "x"))
        test(1, do(locals(), [["lit", "mac", lambda: ["do", "x"]]]))
        test([1], do(locals(), [["lit", "mac", lambda e: e], ["list", 1]]))
        f = ["lit", "mac", lambda e: e]
        test([1], do(locals(), ["f", ["list", 1]]))

if __name__ == '__main__':
    unittest.main()
