import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components

def analyze(B):
    isprime = np.ones(B+2, dtype=bool); isprime[:2]=False
    for i in range(2,int((B+1)**0.5)+1):
        if isprime[i]: isprime[i*i::i]=False
    ax=np.arange(B+1)
    G=np.gcd.outer(ax,ax)
    adm=(G==1)
    adm[:2,:]=False; adm[:,:2]=False
    adm &= (~isprime[:B+1,None]) | (~isprime[None,:B+1])
    idx=-np.ones((B+1,B+1),dtype=np.int64)
    xs,ys=np.nonzero(adm); n=len(xs)
    idx[xs,ys]=np.arange(n)
    rows=[];cols=[]
    h=adm[:-1,:]&adm[1:,:]
    hx,hy=np.nonzero(h)
    rows.append(idx[hx,hy]); cols.append(idx[hx+1,hy])
    v=adm[:,:-1]&adm[:,1:]
    vx,vy=np.nonzero(v)
    rows.append(idx[vx,vy]); cols.append(idx[vx,vy+1])
    r=np.concatenate(rows); c=np.concatenate(cols)
    M=coo_matrix((np.ones(len(r),dtype=np.int8),(r,c)),shape=(n,n))
    ncomp,lab=connected_components(M,directed=False)
    sizes=np.bincount(lab)
    order=np.argsort(sizes)[::-1]
    maxc=np.zeros(ncomp,dtype=np.int64)
    np.maximum.at(maxc,lab,np.maximum(xs,ys))
    top=[(int(sizes[k]),int(maxc[k]),bool(maxc[k]>=B)) for k in order[:4]]
    giant=int(sizes[order[0]])
    print(f"B={B}: verts={n} comps={ncomp} giant={giant} ({100*giant/n:.2f}% of verts) top4={top}")
    return B,n,giant

for B in (400,800,1600,3200,6400):
    analyze(B)
