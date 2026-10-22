# kilit_teorem6_v1.py -- Teorem 6'nin Lean ifadesiyle birebir sayisal sinavi
#   N_c(P_x) + d(x) + [x0<0] = kappa(mu) = #{ozdeger < mu},  x=(Q-mu)^{-1} e0
#   d = #{s gercel kok, s!=0, P'(s)*P_{b.x}(s) > 0}
import numpy as np
rng=np.random.default_rng(2026)
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
ok=0; tot=0; ters=0
for t in range(400):
    N=int(rng.integers(1,6)); Q,lab,b=cvs(N); n=2*N+1
    ev=np.linalg.eigvalsh(Q); mu=rng.uniform(ev.min()-1,ev.max()+1)
    if np.min(np.abs(ev-mu))<1e-3: continue
    x=np.linalg.solve(Q-mu*np.eye(n),np.eye(n)[N])
    if abs(x[N])<1e-8 or abs(x.sum())<1e-8: continue
    P=Ppoly(x,lab); dP=np.polyder(P); Pb=Ppoly(b*x,lab)
    rts=np.roots(P)
    if np.min(np.abs(rts[:,None]-rts[None,:])+np.eye(len(rts))*9)<1e-6: continue   # ayrilabilir
    if np.min(np.abs(rts[:,None]-lab[None,:]))<1e-6: continue                     # etiket disi
    re=rts[np.abs(rts.imag)<1e-9].real; Nc=int(np.sum(rts.imag>1e-9))
    d=int(sum(1 for s in re if abs(s)>1e-12 and np.polyval(dP,s)*np.polyval(Pb,s)>0))
    dters=int(sum(1 for s in re if abs(s)>1e-12 and np.polyval(dP,s)*np.polyval(Pb,s)<0))
    kap=int(np.sum(ev<mu)); tot+=1
    ok+= (Nc+d+(1 if x[N]<0 else 0)==kap)
    ters+= (Nc+dters+(1 if x[N]<0 else 0)==kap)
print("kilit_teorem6_v1.py | ornek:",tot)
print("N_c + d + [x0<0] = kappa(mu):",ok,"/",tot)
print("NEGATIF KONTROL (kosul ters, P'P_b<0):",ters,"/",tot,"tutmali DEGIL")
