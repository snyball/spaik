## Computes average, minimum, maximum, median, and standard deviation
## from lines of numbers.

BEGIN {
    min = 2^64
    max = -1
}

{
    s += $1
    a[n++] = $1
    if ($1 < min) min = $1
    if ($1 > max) max = $1
}

END {
    if (CSVOUT)
        for (i in a)
            print i","a[i] > CSVOUT
    avg = s / n
    asort(a)
    for (i in a)
        s2 += (a[i] - avg)^2
    std = sqrt(s2 / (n - 1))
    print avg, min, max, a[int(n / 2)], std
}
