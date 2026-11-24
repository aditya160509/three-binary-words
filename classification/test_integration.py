"""Exhaust the signed data for small cyclic groups, including nongenerating shifts."""

import unittest
from itertools import product


def differences(word, a, b):
    n = len(word)
    return tuple(
        (word[(i - a) % n] - word[i], word[(i - b) % n] - word[i]) for i in range(n)
    )


def integrates(data, a, b):
    """Integrate by paths on each orbit. Check path consistency and binary range."""
    n = len(data)
    heights = {}
    for root in range(n):
        if root in heights:
            continue
        heights[root] = low = high = 0
        pending = [root]
        while pending:
            i = pending.pop()
            for shift, change in zip((a, b), data[i]):
                j = (i - shift) % n
                value = heights[i] + change
                if j in heights:
                    if heights[j] != value:
                        return False
                else:
                    heights[j] = value
                    low, high = min(low, value), max(high, value)
                    pending.append(j)
        if high - low > 1:
            return False
    return True


class Integration(unittest.TestCase):
    def test_all_small_geometries(self):
        labels = sorted({(v - u, w - u) for u, v, w in product(range(2), repeat=3)})
        for n in range(1, 5):
            for a, b in product(range(n), repeat=2):
                actual = {
                    differences(word, a, b) for word in product(range(2), repeat=n)
                }
                for data in product(labels, repeat=n):
                    self.assertEqual(
                        integrates(data, a, b), data in actual, (n, a, b, data)
                    )

    def test_width_two_example(self):
        data = differences([0, 0, 1, 1, 2, 2, 1, 1], -1, -2)
        self.assertFalse(integrates(data, -1, -2))
        rows = ("00001111", "01011010", "11110000")
        self.assertEqual(
            data, tuple((int(v) - int(u), int(w) - int(u)) for u, v, w in zip(*rows))
        )


if __name__ == "__main__":
    unittest.main()
