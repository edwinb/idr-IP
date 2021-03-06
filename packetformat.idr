include "IPDSL.idr";

cheese = 0;
biscuits = 1;
tea = 2;
coffee = 3;

do using (BIND, CHUNK) {

  IPAddress = do { bits 8; bits 8; 
                   bits 8; bits 8; };

  IPAddress' = do { LISTN (S (S (S (S O)))) (do { bits 8; }); };

  IPint : mkTy IPAddress -> (Int & Int & Int & Int);
  IPint (a ## b ## c ## d) 
        = (value a, value b, value c, value d);

  intIP :  (Int & Int & Int & Int) -> Maybe (mkTy IPAddress);
  intIP (a, b, c, d) with 
       (choose (a < 256), choose (b < 256), 
        choose (c < 256), choose (d < 256)) {
      | (Right _, Right _, Right _, Right _) = 
           Just (bounded a ## bounded b ## bounded c ## bounded d);
      | _ = Nothing;
  }

  syntax V x = BInt x oh;

  labelStr = do { len <- bits 8;
      	          check (value len > 0 && value len < 193);
                  LString (value len);
	        };

  label = do { LIST labelStr;
               bits 2;
	       bits 6; -- Reference to another label, or zero.
	     };

  simplePacket : PacketLang;
  simplePacket = do {
      ver <- bits 2;
      fact (p_bool (value ver == 1));
      label;
      Options 4 [cheese, biscuits, tea];
      IPAddress;
  };
}

-- mkTy gives an Idris type for 'simplePacket' above, the ## separates
-- fields. 'oh' is a proof that some boolean test is done
-- statically. Obviously below we need to check that the given string
-- fits in 16 characters - 'choose' does that test and remembers the
-- result in a form that's usable as a proof.

-- choose : (x:Bool) -> Either (so (not x)) (so x);

-- a ## b ## c ... etc, is the unmarshalled form. 'sendData' and
-- 'getData' convert this from and to a type we might actually want to
-- work with.

convList : List String -> List (mkTy labelStr);
convList Nil = Nil;
convList (Cons y ys) with (choose (strLen y < 256), 
	       	     	   choose (strLen y > 0 && strLen y < 193)) {
    | (Right up, Right down) 
         = Cons (BInt (strLen y) up ## down ## y) (convList ys);
    | _ = Nil;
}

sendData : List String -> mkTy simplePacket;
sendData xs = BInt 1 oh ## oh ## (convList xs ## (BInt 0 oh ## BInt 0 oh)) 
              ## Option tea ## (V 129 ## V 234 ## V 200 ## V 255);

dumpList : List (mkTy labelStr) -> IO ();
dumpList Nil = return II;
dumpList (Cons (_ ## _ ## str) xs) = do { putStrLn str;
	       	       	       	          dumpList xs; };

dumpData : mkTy simplePacket -> IO ();
dumpData (_ ## _ ## (xs ## (_ ## _)) ## teatime ## _) 
      = do { putStrLn (showInt (ovalue teatime));
      	     dumpList xs; };

getIP : mkTy simplePacket -> (Int & Int & Int & Int);
getIP (_ ## _ ## (xs ## (_ ## _ )) ## teatime ## (a ## b ## c ## d))
    = (value a, value b, value c, value d);
