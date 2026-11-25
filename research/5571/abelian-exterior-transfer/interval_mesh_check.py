"""Direct Arb interval-sine cross-check for the uniform Mellin factor on the finite slab."""
from argparse import ArgumentParser
from flint import arb,ctx


def bound():
    pi=arb.pi()
    a=arb(3)/344
    n=32
    radii=[arb(1)/(j*(j+1)) for j in range(1,n+1)]
    def num(r,t):
        return (((r*t).sin().abs_upper())**2+(r/2).sinh()**2).sqrt()
    def shape(h):
        return arb(64)/3*(arb(3)/4).exp()*(1+1/(4*h*h)).sqrt()*(1+1/(2*h*h))
    best=arb(0)
    for k in range(4700,14400):
        h=arb(k)/16
        t=arb(h+arb(1)/32,arb(1)/32)
        ua=num(a,t)/(a*h)
        weight=shape(h)*(arb(1)/66).cosh()*ua**172
        for j,r in enumerate(radii,start=1):
            c=num(r,t)/r
            if j>6:
                c=(c/h).min((r/2).cosh())
            weight*=c
        best=best.max(weight)
    h=arb(900)
    far=shape(h)*(arb(1)/34).cosh()*((a/2).cosh()/(a*h))**172
    for j,r in enumerate(radii[:16],start=1):
        far*=(r/2).cosh()/r
        if j>6:
            far/=h
    print('direct interval sine all finite cells',best)
    print('tail',far)
    assert far < arb('1.242e-154') and best < arb('3.989561711e-114')


if __name__=='__main__':
    p=ArgumentParser()
    p.add_argument('--bits',required=True,type=int)
    ctx.prec=p.parse_args().bits
    bound()
