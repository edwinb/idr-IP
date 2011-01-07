include "packetformat.idr";

getPkt : Maybe Recv -> IO RawPacket;
getPkt Nothing = do { 
    putStrLn "No reply!"; 
    pkt <- newPacket 13;
    return pkt; };
getPkt (Just (mkRecv buf host port)) = do {
    putStrLn ("Ping from " ++ host ++ ":" ++ showInt port);
    return buf; };

fromJust : Maybe a -> IO a;
fromJust (Just x) = return x;
fromJust Nothing = do { putStrLn "FAIL";
	 	      	__Prove_Anything; };


main = do { let p = sendData ["Hello", "World!"];
       	    let pkt = marshal simplePacket p;
	    dumpPacket pkt; 
	    dat <- (fromJust (unmarshal simplePacket pkt));
	    dumpData dat;
	    putStrLn "Opening connection";
	    conn <- TCPConnect "127.0.0.1" 8989;
	    putStrLn "Sending";
	    send conn pkt;
	    putStrLn "Getting reply";
	    echop' <- recv conn;
	    echop <- getPkt echop';
	    dat' <- (fromJust (unmarshal simplePacket echop));
	    dumpPacket echop;
	    dumpData dat';
	    closeSocket conn;
	  };
