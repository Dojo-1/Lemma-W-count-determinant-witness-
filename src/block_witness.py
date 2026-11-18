"""General-n G3 certificates from ratio-primitive blocks (Theorem B in THEOREM.md).

witness(w) returns (r, J, move, start) when some maximal r-free block J of the 3-letter word w
 (R1) contains both other letters p, q and no proper prefix has the p:q ratio of J, and
 one of: M1 J's first letter occurs after J; M2 J's last letter occurs before J;
         M4 J's first letter occurs before J; M5 J's last letter occurs after J;
         M3 J begins and ends with the same letter (|J| >= 3).
Each case names an explicit Moufang move that toggles the node J, and J is absolutely rigid
(boundary/third-letter flanks + R1), so the word has a disconnected class, for every n.
Run: python src/block_witness.py 12   (coverage statistics)
"""
import sys
sys.path.insert(0,'src')
from verify_theorem import interval
from spectra import canon_words
def primitive(J,p,q):
    tp,tq=J.count(p),J.count(q)
    if tp==0 or tq==0: return False
    up=uq=0
    for ch in J[:-1]:
        up+=ch==p;uq+=ch==q
        if up*tq==uq*tp: return False
    return True
def witness(w):
    L=sorted(set(w))
    for r in L:
        p,q=[c for c in L if c!=r]
        i=0;n=len(w)
        while i<n:
            if w[i]==r: i+=1;continue
            j=i
            while j<n and w[j]!=r: j+=1
            J=w[i:j]
            if primitive(J,p,q):
                if J[0] in w[j:]: return (r,J,'M1',i)
                if J[-1] in w[:i]: return (r,J,'M2',i)
                if J[0] in w[:i]: return (r,J,'M4',i)
                if J[-1] in w[j:]: return (r,J,'M5',i)
                if J[0]==J[-1] and len(J)>=3: return (r,J,'M3',i)
            i=j
    return None
if __name__=="__main__":
  for n in range(4,int(sys.argv[1])+1):
      tot=0;miss=[]
      for w in canon_words(n,3):
          if interval(w): continue
          tot+=1
          if witness(w) is None: miss.append(w)
      print(n,'non-interval',tot,'without block witness',len(miss),miss[:12],flush=True)
  