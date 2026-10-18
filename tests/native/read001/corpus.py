#!/usr/bin/env python3
"""The corpus of read001, written into Read.idr: the edges of Chez's syntax,
the texts of random doubles, decimals of 1 to 19 and of 20 to 40 digits, and
the exact halfway points between neighbouring doubles, on them, a digit
below and above, and above by a digit after 900 zeros. A test-time tool;
Python's exact arithmetic gives the halfway points, and its float(), which
rounds correctly, the expected doubles that read001's output agrees with."""
import random, struct
from fractions import Fraction as F

random.seed(2026)

def dbl(b): return struct.unpack('<d', struct.pack('<Q', b))[0]

def exact_decimal(fr):
    """A fraction whose denominator is a power of two, as its exact decimal."""
    n, d = fr.numerator, fr.denominator
    k = d.bit_length() - 1
    assert d == 1 << k
    digits = str(n * 5**k)
    if k == 0: return digits
    digits = digits.rjust(k + 1, '0')
    return digits[:-k] + '.' + digits[-k:]

syntax = ["", "abc", "#x10", "#e1.5", "1e", "1e+", ".", "+.", "-", "+", "5.", ".5", "-.5", "1E5", "1d5", "1s-5", "1F5", "1L5",
          "1.5|53", "1.5|", "1|2", "+inf.0", "-inf.0", "+nan.0", "-nan.0", "inf.0", "nan.0", "-0", "-0.0", "-0e5", "-.0", "0", "+0.0",
          "00012.500", " 1", "1 ", "1_000", "1/2", "+5", "-5", "1e400", "-1e400", "1e-400", "1e99999999999", "1e-99999999999",
          "1..5", "1.5.", "e5", "1e5.0", "123456789012345678901234567890", "0.000000000000000000000000000001234"]
numeric = []
for _ in range(300):
    b = random.getrandbits(63)
    if (b >> 52) == 0x7FF: continue
    x = dbl(b); numeric += [repr(x), "%.17e" % x]
for _ in range(300):
    n = random.randint(1, 19); w = random.randint(0, 10**n - 1); q = random.randint(-360, 330)
    numeric.append(f"{w}e{q}")
for _ in range(150):
    n = random.randint(20, 40); w = random.randint(10**(n-1), 10**n - 1); q = random.randint(-340, 300)
    numeric.append(f"{w}e{q}")
for _ in range(120):
    b = random.choice([random.getrandbits(63) % 0x7FE0000000000000, random.getrandbits(52), random.randrange(1 << 61)])
    mid = exact_decimal((F(dbl(b)) + F(dbl(b + 1))) / 2)
    numeric += [mid, mid + "0" * 50, mid + "0" * 900 + "1"]
    if '.' in mid:
        if mid[-1] != '0': numeric.append(mid[:-1] + str(int(mid[-1]) - 1))
        numeric.append(mid + "1")
print("\n".join(syntax + numeric))
