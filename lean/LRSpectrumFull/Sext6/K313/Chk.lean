/- Core-only Bool checker for CleanPrime (lowest-bit-first, last-pick intersection). No Mathlib. -/
namespace KC
def DB : Nat := 228824044090659455778900855050322128002759787305348791014476408721956007679
def DBT : Nat := 31430279023242600257529497506287036036019168029105233162645390034391866911629632350076471424210961754254718268439737418263262318822914554758855049569522843987302801349165237832974586000963846010956811751549831411711105617458852908279926477203618154471799694614502221199747423266294403225404631515151180054899799169565338119294851039197679143508146405692927935937080419529226568725384779016864573633792975770222278171658546845749390026621021400318686457757010888252786879147650629209609297000732903884421172727272712305519601057190071456929667238252846501849926836362671640976969355839074445984751473161209484496994560
def clr (x : Nat) : Nat := x &&& (x - 1)
def lowb (x : Nat) : Nat := x ^^^ clr x
def idx (b : Nat) : Nat := (DBT >>> (8 * (((b * DB) % (1 <<< 256)) >>> 248))) % 256
def msk (T M W r : Nat) : Nat := (T >>> (r * W)) % M
def red (p x : Nat) : Nat := let y := x % p; if 2 * y > p then p - y else y
def coverB (p r a : Nat) : Bool := decide (7 * min ((r * a) % p) (p - (r * a) % p) ≤ p)
def cvb (p h r a : Nat) : Bool :=
  decide (1 ≤ r) && decide (r ≤ h) && decide (1 ≤ a) && decide (a ≤ h) && coverB p r a
def tabOK (p h T M W : Nat) : Bool :=
  (List.range 256).all fun r => (List.range W).all fun a => (msk T M W r).testBit a == cvb p h r a
def mk6 (p u : Nat) : Nat :=
  (1 <<< red p (u*1)) ||| (1 <<< red p (u*2)) ||| (1 <<< red p (u*3)) ||| (1 <<< red p (u*4)) ||| (1 <<< red p (u*5)) ||| (1 <<< red p (u*6))
def anyCls (p h s : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | f+1, rest => if rest == 0 then false else
      ((decide (0 < idx (lowb rest)) && decide (idx (lowb rest) ≤ h) && (mk6 p (idx (lowb rest)) == s)) || anyCls p h s f (clr rest))
def leafB (p h s : Nat) : Bool := anyCls p h s 8 s
def kidsB (child : Nat → Nat → Nat → Bool) (T M W unc s : Nat) : Nat → Nat → Nat → Bool
  | 0, cand, _ => cand == 0
  | f+1, cand, ex => cand == 0 ||
      (child (unc ^^^ (unc &&& msk T M W (idx (lowb cand)))) ex (s ||| lowb cand) &&
       kidsB child T M W unc s f (clr cand) (ex ||| lowb cand))
def andAll (T M W : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f+1, rest, acc => if rest == 0 || acc == 0 then acc else
      andAll T M W f (clr rest) (acc &&& msk T M W (idx (lowb rest)))
def leavesB (p h s : Nat) : Nat → Nat → Bool
  | 0, cand => cand == 0
  | f+1, cand => cand == 0 || (leafB p h (s ||| lowb cand) && leavesB p h s f (clr cand))
def lastB (p h T M W unc ex s : Nat) : Bool :=
  let m := msk T M W (idx (lowb unc))
  leavesB p h s 240 (andAll T M W 240 (clr unc) (m ^^^ (m &&& ex)))
def stepB (p h T M W : Nat) (lp : Bool) (k : Nat) (rec : Nat → Nat → Nat → Bool) (unc ex s : Nat) : Bool :=
  if unc == 0 then leafB p h s
  else if lp && k == 0 then lastB p h T M W unc ex s
  else
    let m := msk T M W (idx (lowb unc))
    kidsB rec T M W unc s 240 (m ^^^ (m &&& ex)) ex
def dfsB (p h T M W : Nat) (lp : Bool) : Nat → Nat → Nat → Nat → Bool
  | 0, unc, _, s => if unc == 0 then leafB p h s else true
  | k+1, unc, ex, s => stepB p h T M W lp k (dfsB p h T M W lp k) unc ex s
def topB (p h T M W : Nat) (lp : Bool) (m : Nat) (rec : Nat → Nat → Nat → Bool) : Nat → Nat → Nat → Nat → Bool
  | 0, unc, ex, s => rec unc ex s
  | D+1, unc, ex, s => stepB p h T M W lp (m + D) (topB p h T M W lp m rec D) unc ex s
def unc0 (T M W : Nat) : Nat := ((M - 1) ^^^ 1) ^^^ msk T M W 1
def memB (L : List (Nat × Nat × Nat)) (u e s : Nat) : Bool := L.any fun x => x.1 == u && x.2.1 == e && x.2.2 == s
end KC
