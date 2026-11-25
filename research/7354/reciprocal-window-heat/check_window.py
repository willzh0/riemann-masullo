"""Independent finite quadratures for the log-shift, endpoint orientation and spatial floor."""
import math
import numpy as np
from numpy.polynomial.legendre import leggauss
from numpy.polynomial.hermite import hermgauss
from scipy.special import sici

DELTA = 0.4
A, B = 1 / (1 + DELTA), 1 / (1 - DELTA)
G, WG = leggauss(14)
H, WH = hermgauss(30)


def integral(f, low, high, size):
    n = max(6, math.ceil((high - low) * 3.5 * size))
    width = (high - low) / n
    x = low + (np.arange(n)[:, None] + (G + 1) / 2) * width
    return width / 2 * np.sum(f(x) * WG)


def smooth(log_g):
    t = (np.abs(log_g) - .12) / .18
    q = np.clip(t, 1e-6, 1-1e-6)
    left = np.exp(-1 / q)
    right = np.exp(-1 / (1-q))
    cutoff = np.where(t <= 0, 1, np.where(t >= 1, 0, right / (left + right)))
    return (1 + .65 * log_g + log_g**2) * cutoff


def boundary(log_g):
    return 1 + .65 * log_g + log_g**2


def kernel(r, phase):
    y = 2 * math.pi * r * phase
    return np.divide(sici(y)[0], math.pi * phase,
                     out=np.full_like(phase, 2*r), where=phase != 0)


def haar_ambient(r, z, test, floor=0):
    m = math.exp(min(0, z))
    def value(y):
        phase = np.expm1(-y-z)
        data = kernel(r*m, phase) + kernel(r*m, phase+2)
        if floor:
            data -= kernel(floor*m, phase) + kernel(floor*m, phase+2)
        return test(y) * np.exp(-(y+z)/2) * data
    return integral(value, math.log(A), math.log(B), max(r, 1))


def phase_ambient(r, z, test, move=True):
    shift = math.exp(-z)
    m = math.exp(min(0,z))
    lo, hi = (shift*(1-DELTA)-1, shift*(1+DELTA)-1) if move else (-DELTA, DELTA)
    def value(c):
        return (test(-z-np.log1p(c)) / np.sqrt(1+c) *
                (kernel(r*m,c) + kernel(r*m, c+2)))
    return integral(value, lo, hi, max(r, 1))


def cold_floor(r, test):
    def value(y):
        g = np.exp(y)
        cm, cp = 1/g-1, 1/g+1
        v = 2*math.pi*r
        polar = g/math.pi*(cp*sici(v*cp)[0]-cm*sici(v*cm)[0]+(np.cos(v*cp)-np.cos(v*cm))/v)
        return test(y)*np.exp(-y/2)*(kernel(r,cm)+kernel(r,cp)-polar)
    return integral(value, math.log(A), math.log(B), max(r, 1))


for z in (-.07,.04):
    direct = haar_ambient(80,z,boundary)
    moved = phase_ambient(80,z,boundary)
    wrong = phase_ambient(80,z,boundary,move=False)
    print(f"endpoint z={z:+.2f} coordinate error={abs(direct-moved):.3g} fixed-window error={abs(direct-wrong):.5g}")
    assert abs(direct-moved) < 2e-10 and abs(direct-wrong) > .005
for r in (16, 64, 256):
    tau = 5e-4
    z = 2*math.sqrt(tau)*H
    hot = np.dot(WH,[phase_ambient(r,v,smooth) for v in z]) / math.sqrt(math.pi)
    cold = phase_ambient(r,0,smooth)
    coeff = np.dot(WH,smooth(-z))/math.sqrt(math.pi) - smooth(0)
    print(f"R={r:3} hot-cold={hot-cold:+.6f} E[w(exp(-Z))]-w(1)={coeff:+.6g} twice-tau={2*tau:.6g}")
print("cold floor, R_floor=.01,.1,.5:", *(f"{cold_floor(r,smooth):.9g}" for r in (.01,.1,.5)))
