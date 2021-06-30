#!/usr/bin/env python3

def sieve(n):
    field = []
    primes = []
    for i in range(0, n+1):
        field.append(False)
    for f in range(2, n+1):
        if not field[f]:
            primes.append(f)
            for j in range(f, n+1, f):
                field[j] = True
    return primes

sieve(100000)
