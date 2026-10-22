# indeks_teorem5a_v1.py -- Teorem 5(a)'nin Lean ifadesiyle birebir sayisal sinavi
#   lambda basit ozdeger, xi cift ozvektor, xi notin R e0:  N_c(P_xi) + d(xi) = kappa(lambda)
#   d = #{s gercel kok, s!=0, P'(s)*P_{b.xi}(s) > 0}
import numpy as np
rng=np.random.default_rng(55)
def cvs(N):
    lab=np.arange(-N,N+1).astype(float); n=2*N+1
    a=rng.normal(size=N+1); a=np.concatenate([a[:0:-1],a])
    bh=rng.normal(size=N); b=np.concatenate([-bh[::-1],[0.0],bh])
    Q=np.diag(a)
    for i in range(n):
        for j in range(n):
            if i!=j: Q[i,j]=(b[i]-b[j])/(lab[i]-lab[j])
    return Q,lab,b
def Ppoly(w,lab):
    n=len(lab); poly=np.zeros(1)
    for k in range(n):
        pk=np.array([1.0])
        for j in range(n):
            if j!=k: pk=np.polymul(pk,np.array([-1.0,lab[j]]))
        poly=np.polyadd(poly,w[k]*pk)
    return poly
ok=tot=ters=0
for t in range(300):
    N=int(rng.integers(1,6)); Q,lab,b=cvs(N); n=2*N+1
    ev,V=np.linalg.eigh(Q)
    for m in range(n):
        xi=V[:,m]; lam=ev[m]
        if np.min(np.abs(np.delete(ev,m)-lam))<1e-6: continue            # basit
        if np.max(np.abs(xi-xi[::-1]))>1e-8: continue                     # cift
        if np.max(np.abs(np.delete(xi,N)))<1e-8: continue                 # xi notin R e0
        P=Ppoly(xi,lab); dP=np.polyder(P); Pb=Ppoly(b*xi,lab); rts=np.roots(P)
        if len(rts)>1 and np.min(np.abs(rts[:,None]-rts[None,:])+np.eye(len(rts))*9)<1e-6: continue
        if np.min(np.abs(rts[:,None]-lab[None,:]))<1e-6: continue
        re=rts[np.abs(rts.imag)<1e-9].real; Nc=int(np.sum(rts.imag>1e-9))
        d=int(sum(1 for s in re if abs(s)>1e-12 and np.polyval(dP,s)*np.polyval(Pb,s)>0))
        dt=int(sum(1 for s in re if abs(s)>1e-12 and np.polyval(dP,s)*np.polyval(Pb,s)<0))
        kap=int(np.sum(ev<lam-1e-12)); tot+=1
        ok+=(Nc+d==kap); ters+=(Nc+dt==kap)
print("indeks_teorem5a_v1.py | ornek:",tot)
print("N_c + d = kappa(lambda):",ok,"/",tot)
print("NEGATIF KONTROL (kosul ters):",ters,"/",tot,"tutmali DEGIL")
