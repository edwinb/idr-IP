
-- Some proofs about primitive operations - we just have to trust these.

-- Not that this is actually true if x+y overflows! Whole thing works
-- under the assumption that it doesn't.

ltAdd : (y:Int) -> (so (y>0)) -> so (x+y >= x);
ltAdd y = __Prove_Anything _ _ oh;

addSub : (x:Int) -> (y:Int) -> (x = ((y + x) - y));
addSub x y = __Suspend_Disbelief ((y+x)-y) x;

check : (T:Bool) -> Either (so T) (so (not T));
check True = Left oh;
check False = Right oh;

unsafeCoerce : {a:Set} -> {b:Set} -> a -> b;
unsafeCoerce a ?= a; [doCoerce]

doCoerce proof {
	%intro;
	%rewrite __Suspend_Disbelief X0 X;
	%refine value;
	%qed;
};

isThatSo : (x:Bool) -> Tactic;
isThatSo x = TTry (TFill oh)
	    (TTry TTrivial 
	    (TFail "Not so!"));

syntax mk_so = [tryproof %intro; %decide isThatSo; %qed];
syntax bounded x = BInt x mk_so;


