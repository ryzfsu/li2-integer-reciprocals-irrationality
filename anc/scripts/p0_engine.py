#!/usr/bin/env python3
"""Directed-Arb dual lower bound for the complete positive-base energy.

No optimizer value is trusted. The reference is exact rational real-cell
masses and an exactly nonnegative finite Fejer mixture on the ellipse.
Every min integral is bounded on its whole domain, including infinity.
"""
import argparse
import csv
import json
import math
import time
from fractions import Fraction as F
from pathlib import Path
from flint import arb, ctx

CELL_DENOMINATOR = 10**10

def ar(q):
    q=F(q)
    return arb(q.numerator)/q.denominator

def box(a,b):
    a,b=F(a),F(b)
    return arb(ar((a+b)/2),ar((b-a)/2))

def rational_lower(v):
    """Mint a rational lower bound, then prove its direction with Arb.

    Binary floats only suggest the integer. This checked comparison, rather
    than the float conversion, is the proof of the emitted cell bound.
    """
    q=F(math.floor(float(v.lower())*CELL_DENOMINATOR)-1,CELL_DENOMINATOR)
    assert v.lower()>ar(q)
    return q

def write_cells(path,rows):
    with Path(path).open('w',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(['left_endpoint','right_endpoint','rational_potential_lower_bound'])
        writer.writerows(rows)

def f_point(x):
    if x == 0:return arb(0)
    return x*(abs(x).log()-1)

def real_primitive(x):
    """Hull of u(log|u|-1); its only critical points are -1,+1."""
    x=arb(x)
    ans=f_point(x.lower()).union(f_point(x.upper()))
    for u,v in [(0,0),(-1,1),(1,-1)]:
        if x.contains(u):ans=ans.union(v)
    return ans

def complex_primitive(x,y):
    """∫log|u+iy|du, up to a constant depending only on y.

    y may cross zero. The expression uses |y| and has no log branch cut.
    All uses in this checker have x^2+y^2 strictly positive.
    """
    y=abs(y)
    log_radius=(x*x+y*y).log()/2
    return x*(log_radius-1)+y*arb.atan2(x,y)

def second_primitive(v):
    v=F(v)
    if v == 0:return arb(0)
    x=ar(v)
    return x*x*(abs(x).log()/2-ar(F(3,4)))

def jumps(edges,masses,den):
    rho=[F(m,den)/(b-a) for a,b,m in zip(edges[:-1],edges[1:],masses)]
    prev=F(0); result=[]
    for edge,density in zip(edges,rho+[F(0)]):
        change=density-prev
        if change:result.append((edge,ar(change)))
        prev=density
    return rho,result

class Certificate:
    def __init__(self,ref,base_q=2,negative=False):
        self.r=ref; self.den=ref['denominator']; self.K=ref['fejer_degree']
        if base_q < 2:
            raise ValueError('base_q must be at least 2')
        self.base_q=base_q; self.negative=negative
        self.xi,self.A,self.B=[F(v) for v in ref['geom']]
        assert self.xi-self.A==F(-751,5000)
        assert self.xi+self.A==F(1504,625)
        assert self.A>self.B>0
        self.c=(self.A+self.B)/2; self.q=(self.A-self.B)/(self.A+self.B)
        self.ac,self.aq,self.ax=ar(self.c),ar(self.q),ar(self.xi)
        self.logc=self.ac.log(); self.ln2=arb(2).log()
        self.logq=arb(base_q).log()
        self.const=ar(F(9,2))-2*self.ln2
        self.int_logs=ar(F(1,2))*(-self.ln2-1)
        self.pe=[F(v) for v in ref['pinned_edges']]
        self.te=[F(v) for v in ref['frequency_edges']]
        self.pm=ref['pinned_mass']; self.tm=ref['frequency_mass']; self.cw=ref['contour_mass']
        self.pr,self.pj=jumps(self.pe,self.pm,self.den)
        self.tr,self.tj=jumps(self.te,self.tm,self.den)
        assert self.pe[0]==F(1,4) and self.pe[-1]==F(5,4)
        assert self.te[0]==F(1,2) and self.te[-1]<=F(9,2)
        assert min(self.pm+self.tm+self.cw)>=0
        assert all(0<=v<=1 for v in self.pr+self.tr)
        assert sum(self.pm)+sum(self.cw)==self.den and sum(self.tm)==self.den
        assert self.cw==self.cw[::-1], 'Exact cosine symmetry is required.'
        self.M=ar(F(sum(self.cw),self.den))
        nc=len(self.cw)
        assert nc==ref['contour_grid_count']
        self.mom=[]
        for n in range(1,self.K+1):
            m=arb(0)
            for j,mass in enumerate(self.cw):
                if mass:
                    angle=arb.pi()*ar(F(n*(2*j+1),nc))
                    m+=ar(F(mass,self.den))*angle.cos()
            self.mom.append(ar(F(self.K+1-n,self.K+1))*m)
        self.coeff=[m/n for n,m in enumerate(self.mom,1)]
        self.qpow=[self.aq**n for n in range(1,self.K+1)]
        self.cont_coeff=[(1+qn)*m/n for n,(qn,m) in enumerate(zip(self.qpow,self.mom),1)]

    def lint_real(self,x,a,b,plus=False):
        if plus:return real_primitive(x+ar(b))-real_primitive(x+ar(a))
        return real_primitive(x-ar(a))-real_primitive(x-ar(b))

    def lint_complex(self,x,y,a,b,plus=False):
        if plus:return complex_primitive(x+ar(b),y)-complex_primitive(x+ar(a),y)
        return complex_primitive(x-ar(a),y)-complex_primitive(x-ar(b),y)

    def lp_real(self,x,jumps,plus=False):
        if plus:return -sum((v*real_primitive(x+ar(e)) for e,v in jumps),arb(0))
        return sum((v*real_primitive(x-ar(e)) for e,v in jumps),arb(0))

    def lp_complex(self,x,y,jumps,plus=False):
        if plus:return -sum((v*complex_primitive(x+ar(e),y) for e,v in jumps),arb(0))
        return sum((v*complex_primitive(x-ar(e),y) for e,v in jumps),arb(0))

    def nu_inside(self,x):
        w=(x-self.ax)/self.ac
        prev=arb(2); curr=w
        ans=self.M*self.logc
        for n,b in enumerate(self.coeff,1):
            if n>1:prev,curr=curr,w*curr-self.aq*prev
            ans-=b*curr
        return ans

    def nu_contour(self,u):
        return self.M*self.logc-sum((b*(n*u).cos() for n,b in enumerate(self.cont_coeff,1)),arb(0))

    def nu_out(self,t):
        u=t+self.ax
        d=(u*u-4*self.ac*self.ac*self.aq).sqrt()
        s=-2*self.ac/(u+d)
        ans=self.M*((u+d)/2).log()
        sn=arb(1)
        for b in self.cont_coeff:
            sn*=s; ans-=b*sn
        return ans

    def nu_inside_integral(self,x):
        """Exact antiderivative on the pinned interval; finite polynomial."""
        w=(x-self.ax)/self.ac
        s=[arb(2),w]
        for n in range(2,self.K+2):s.append(w*s[-1]-self.aq*s[-2])
        result=self.M*self.logc*x
        for n,b in enumerate(self.coeff,1):
            integral=s[2]/2 if n==1 else s[n+1]/(n+1)-self.aq*s[n-1]/(n-1)
            result-=self.ac*b*integral
        return result

    def nu_out_integral(self,t):
        """Exact external antiderivative, using t+xi=-c/s-c*q*s."""
        u=t+self.ax
        delta=(u*u-4*self.ac*self.ac*self.aq).sqrt()
        s=-2*self.ac/(u+delta)
        d=self.ac*self.aq
        result=self.M*(u*((u+delta)/2).log()-delta)
        powers=[arb(1)]
        for n in range(1,self.K+2):powers.append(powers[-1]*s)
        for n,b in enumerate(self.cont_coeff,1):
            integral=self.ac*abs(s).log()-d*powers[2]/2 if n==1 else self.ac*powers[n-1]/(n-1)-d*powers[n+1]/(n+1)
            result-=b*integral
        return result

    def Wpin(self,x):
        V=self.lint_real(x,F(1,4),F(5,4))+self.lint_real(x,0,2)-x*self.logq-self.lint_real(x,0,F(1,2),True)+self.int_logs
        return V-2*self.lp_real(x,self.pj)-2*self.nu_inside(x)-self.lp_real(x,self.tj,True)

    def Wcont(self,u):
        x=self.ax+ar(self.A)*u.cos(); y=ar(self.B)*u.sin()
        V=self.lint_complex(x,y,F(1,4),F(5,4))+self.lint_complex(x,y,0,2)-x*self.logq-self.lint_complex(x,y,0,F(1,2),True)+self.int_logs
        branch=arb.pi()*y if self.negative else arb(0)
        return V-2*self.lp_complex(x,y,self.pj)-2*self.nu_contour(u)-self.lp_complex(x,y,self.tj,True)+branch

    def Wfreq(self,t):
        V=self.lint_real(t,F(1,4),F(5,4),True)+self.lint_real(t,0,2,True)-self.lint_real(t,0,F(1,2))+self.int_logs+t*self.logq
        return V-2*self.lp_real(t,self.tj)-self.lp_real(t,self.pj,True)-self.nu_out(t)

    def rect(self,e1,r1,e2,r2,plus=False):
        ans=arb(0)
        cache={}
        def G(v):
            if v not in cache:cache[v]=second_primitive(v)
            return cache[v]
        for a,b,rho in zip(e1[:-1],e1[1:],r1):
            if not rho:continue
            for c,d,sig in zip(e2[:-1],e2[1:],r2):
                if not sig:continue
                v=G(b+d)-G(a+d)-G(b+c)+G(a+c) if plus else G(b-c)-G(a-c)-G(b-d)+G(a-d)
                ans+=ar(rho*sig)*v
        return ans

    def Q(self):
        def endpoint_integral(fun,edges,rho):
            ans=arb(0)
            for a,b,density in zip(edges[:-1],edges[1:],rho):
                if density:ans+=ar(density)*(fun(ar(b))-fun(ar(a)))
            return ans
        parts=dict(pin_pin=self.rect(self.pe,self.pr,self.pe,self.pr),
                   freq_freq=self.rect(self.te,self.tr,self.te,self.tr),
                   pin_freq=self.rect(self.pe,self.pr,self.te,self.tr,True),
                   pin_contour=endpoint_integral(self.nu_inside_integral,self.pe,self.pr),
                   freq_contour=endpoint_integral(self.nu_out_integral,self.te,self.tr),
                   contour_contour=self.M*self.M*self.logc-sum(((1+qn)*m*m/n for n,(qn,m) in enumerate(zip(self.qpow,self.mom),1)),arb(0)))
        q=parts['pin_pin']+parts['freq_freq']+parts['pin_freq']+2*parts['pin_contour']+parts['freq_contour']+parts['contour_contour']
        return q,parts

    def contour_check(self,hq,initial,max_depth,receipt_path):
        # The negative branch adds pi*Im(z), so conjugation does not preserve
        # W_eta. Check both halves instead of reflecting the upper half.
        count = 2 * initial if self.negative else initial
        pending=[(F(j,initial),F(j+1,initial),0) for j in range(count)]
        h=ar(hq)
        checked=0; least=None; deepest=0; rows=[]
        while pending:
            a,b,depth=pending.pop()
            v=self.Wcont(arb.pi()*box(a,b))
            assert v.is_finite(), f'nonfinite contour interval {a},{b}'
            if v.lower()>=h:
                checked+=1; deepest=max(deepest,depth)
                if least is None or v.lower()<least:least=v.lower()
                q=max(rational_lower(v),hq)
                assert v.lower()>=ar(q)
                rows.append([str(a),str(b),str(q)])
            else:
                if depth>=max_depth:
                    raise ValueError(f'Contour threshold fails at {a},{b}, W={v}, h={h}')
                mid=(a+b)/2
                pending.extend([(mid,b,depth+1),(a,mid,depth+1)])
        write_cells(receipt_path,rows)
        cover = '[0,2pi] with both halves checked; CSV endpoints are u/pi' if self.negative else '[0,pi] plus exact conjugation symmetry; CSV endpoints are u/pi'
        return dict(cover=cover, accepted_cells=checked,
                    deepest_refinement=deepest, minimum_directed_lower_bound=str(least),
                    cell_lower_bounds_csv=Path(receipt_path).name)

    def positive_integral(self,fun,a,b,hq,n,receipt_path):
        step=(b-a)/n; total=F(0); active=0; rows=[]
        for j in range(n):
            v=fun(box(a+j*step,a+(j+1)*step))
            assert v.is_finite(), f'nonfinite potential at cell {j}/{n}: {v}'
            # h - inf W is an upper bound on the positive part on this cell.
            q=rational_lower(v)
            contribution=max(hq-q,0)
            total+=step*contribution
            if contribution>0:active+=1
            rows.append([str(a+j*step),str(a+(j+1)*step),str(q)])
        write_cells(receipt_path,rows)
        bound=ar(total)
        return bound,dict(cells=n, positive_bound_cells=active, upper_bound=str(bound.upper()),
                          exact_rational_upper_bound=str(total),cell_lower_bounds_csv=Path(receipt_path).name)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--reference',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--q',type=int,default=2)
    p.add_argument('--negative',action='store_true')
    p.add_argument('--h-eta',default='-669/200')
    p.add_argument('--h-mu',default='71/25')
    p.add_argument('--target',default='199/100')
    p.add_argument('--require-target',action='store_true')
    p.add_argument('--real-cells',type=int,default=8192)
    p.add_argument('--contour-initial',type=int,default=256)
    p.add_argument('--contour-max-depth',type=int,default=10)
    args=p.parse_args(); ctx.dps=45; start=time.time()
    ref=json.loads(Path(args.reference).read_text()); c=Certificate(ref,args.q,args.negative)
    heq=F(args.h_eta); hmq=F(args.h_mu); target=F(args.target)
    he=ar(heq); hm=ar(hmq); tail=F(81,10)
    receipt_dir=Path(args.out).parent
    print('Exact rational reference feasible; finite Fejer moments computed.',flush=True)
    q,parts=c.Q()
    print('Q_log:',q,' elapsed:',round(time.time()-start,2),flush=True)
    cover=c.contour_check(heq,args.contour_initial,args.contour_max_depth,receipt_dir/'contour_cells.csv')
    print('Whole contour:',cover,' elapsed:',round(time.time()-start,2),flush=True)
    P,pc=c.positive_integral(c.Wpin,F(1,4),F(5,4),heq,args.real_cells,receipt_dir/'pinned_cells.csv')
    print('Pinned positive part upper:',P.upper(),' elapsed:',round(time.time()-start,2),flush=True)
    T,tc=c.positive_integral(c.Wfreq,F(1,2),tail,hmq,args.real_cells*2,receipt_dir/'frequency_cells.csv')
    print('Frequency finite positive part upper:',T.upper(),' elapsed:',round(time.time()-start,2),flush=True)
    endpoint=c.Wfreq(ar(tail))
    assert endpoint.lower()>hm
    # For t≥81/10, positive reference masses, Re z≥−751/5000,
    # and reference frequency support≤9/2 give
    # Wmu'≥ln2−1/[2(t−1/2)]+3/(t+2)−2/(t−9/2)−1/(t−751/5000).
    # This RHS is increasing: combine 2/(t−9/2)^2+1/(t−751/5000)^2
    # against 3/(t+2)^2, while 1/[2(t−1/2)^2] is positive.
    tail_slope=F(693,1000)-1/(2*(tail-F(1,2)))+3/(tail+2)-2/(tail-F(9,2))-1/(tail-F(751,5000))
    assert tail_slope>F(1,50)
    assert c.ln2.lower()>ar(F(693,1000))
    lower=c.const+q+he+hm-P.upper()-T.upper()
    rational=F(math.floor(float(lower.lower())*10**6)-1,10**6)
    assert lower.lower()>ar(rational)
    out=dict(status='EXACT_CONTINUUM_DUAL', target=str(target), base_q=args.q,
             sign='negative' if args.negative else 'positive', reference=Path(args.reference).name,
             decimal_precision=ctx.dps,h_eta=str(heq),h_mu=str(hmq),
             Q_log_interval=str(q),Q_log_directed_lower_bound=str(q.lower()),Q_parts={k:str(v) for k,v in parts.items()},
             contour=cover,pinned_positive_part=pc,frequency_positive_part=tc,
             tail=dict(endpoint='81/10',endpoint_potential_interval=str(endpoint),
                       derivative_rational_lower_bound=str(tail_slope),
                       derivative_strictly_greater_than='1/50',positive_part_tail='exactly zero'),
             dual_interval=str(lower),certified_rational_lower_bound=str(rational),
             alpha_gt_1_98=bool(lower.lower()>ar(F(99,50))),
             alpha_gt_1_99=bool(lower.lower()>ar(F(199,100))),
             alpha_gt_target=bool(lower.lower()>ar(target)),
             runtime_seconds=time.time()-start,
             scope='Full continuum infimum only; uniform determinant passage is a separate obligation.')
    Path(args.out).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,sort_keys=True),flush=True)
    if args.require_target:
        assert out['alpha_gt_target'], 'Target not certified; inspect directed receipt.'

if __name__=='__main__':main()
