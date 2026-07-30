import numpy as np, json
from collections import deque
from math import gcd
from sympy import isprime
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components

B=3200
isp=np.ones(B+2,dtype=bool); isp[:2]=False
for i in range(2,int((B+1)**0.5)+1):
    if isp[i]: isp[i*i::i]=False
ax=np.arange(B+1); G=np.gcd.outer(ax,ax)
adm=(G==1); adm[:2,:]=False; adm[:,:2]=False
adm &= (~isp[:B+1,None])|(~isp[None,:B+1])
idx=-np.ones((B+1,B+1),dtype=np.int64)
xs,ys=np.nonzero(adm); n=len(xs); idx[xs,ys]=np.arange(n)
h=adm[:-1,:]&adm[1:,:]; hx,hy=np.nonzero(h)
v=adm[:,:-1]&adm[:,1:]; vx,vy=np.nonzero(v)
r=np.concatenate([idx[hx,hy],idx[vx,vy]]); c=np.concatenate([idx[hx+1,hy],idx[vx,vy+1]])
M=coo_matrix((np.ones(len(r),dtype=np.int8),(r,c)),shape=(n,n))
nc,lab=connected_components(M,directed=False)
sizes=np.bincount(lab); g=int(np.argmax(sizes))
members=np.nonzero(lab==g)[0]
gx,gy=xs[members],ys[members]
i0=int(np.argmin(gx+gy))
start=(int(gx[i0]),int(gy[i0]))
print(f"giant size {sizes[g]}, start {start}, min coords x>={gx.min()} y>={gy.min()}")

prev={}; dq=deque([start]); seen={start}; best=start
while dq:
    x,y=dq.popleft()
    if x>best[0]: best=(x,y)
    for nx,ny in ((x+1,y),(x-1,y),(x,y+1),(x,y-1)):
        if 2<=nx<=B and 2<=ny<=B and adm[nx,ny] and (nx,ny) not in seen:
            seen.add((nx,ny)); prev[(nx,ny)]=(x,y); dq.append((nx,ny))
path=[best]
while path[-1]!=start: path.append(prev[path[-1]])
path=path[::-1]
ok=True
for i,(x,y) in enumerate(path):
    if not(min(x,y)>1 and gcd(x,y)==1 and (not isprime(x) or not isprime(y))):
        ok=False; print("BAD VERTEX",(x,y)); break
    if i>0:
        px,py=path[i-1]
        if abs(px-x)+abs(py-y)!=1: ok=False; print("BAD STEP",path[i-1],(x,y)); break
ys2=[y for _,y in path]
print(f"reached {best}, path length {len(path)}, VERIFIED={ok}")
print(f"y range along path: {min(ys2)}..{max(ys2)}")
json.dump(path,open("path_witness_3200.json","w"))
