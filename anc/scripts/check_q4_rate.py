#!/usr/bin/env python3
"""Check the printed outward upper bound for the q=4 V arithmetic rate."""
from fractions import Fraction

from flint import arb


N40 = 132263363803421925450338622847809742317124551497
D40 = 26020759561732371877438650035601516684254668800
TAU4_UPPER = Fraction(3552293941, 10**9)

tau4 = arb(N40) / D40 - arb(53) / 48 * arb(4).log()
upper = arb(TAU4_UPPER.numerator) / TAU4_UPPER.denominator
assert tau4.upper() < upper

print(f"A40={N40}/{D40}")
print(f"tau4={tau4}")
print(f"certified upper={TAU4_UPPER}")
print("strict_upper=True")
