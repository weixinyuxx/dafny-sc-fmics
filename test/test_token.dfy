include "../token/token.dfy"

class test_token {

    method test_init_unit()
    {
        // a point-like unit test
        var sender := new UserAccount(10); 

        // enough ETH
        var msg := Msg(sender, 10);
        var token := new Token(msg);
        assert token.minter == sender;
        // assert token.balances == map[];
        assert sum(token.balances) == token.totalAmount;
        assert token.balance == msg.value;
        // assert token.isContract;

        // not enough ETH
        msg := Msg(sender, 100);
        token := new Token(msg); // !!!: this should not pass (precondition of init)

    }
    method test_init_property(msg:Msg, token:Token)
    {
        // problem: statement context object cannot be ==?
        // var t := new Token(msg);
        // assert t == token ==> t.minter == msg.sender;
        // assert t != token;
        // assert false;

        // problem: cannot call method in forall statement
        // assert forall msg:Msg, token:Token |  :: true;
    }


    /**
     *  Mint some new tokens.
     *
     *  @param  to      Target Address.
     *  @param  amount  The amount to receiving the newly minted tokens
     *  @param  msg     The `msg` content.
     *  @param  gas     The gas allocated to the execution.
     *  @returns        The gas left after executing the call.
     */
    method test_mint()
    {
        var sender := new UserAccount(100); // actually, how to identify the sender?
        var msg := Msg(sender, 10);
        var token := new Token(msg);
        var oldTotal := token.totalAmount;
        var oldBalances := token.balances;

        var dest := new UserAccount(10);

        // // mint by another account
        // var g := token.mint(dest, 100, Msg(dest, 10), 100); // should not be able to call (not by minter)

        // called by minter
        var gasUsed := token.mint(dest, 100, Msg(sender, 10), 100);
        assert token.totalAmount == sum(token.balances);
        assert token.totalAmount == oldTotal + 100;

        assert forall acc | acc in oldBalances && acc != dest :: token.balances[acc] == oldBalances[acc];
        assert forall acc | acc in token.balances.Keys - oldBalances.Keys :: acc == dest;
        assert if dest in oldBalances then token.balances[dest] == oldBalances[dest] + 100
            else token.balances[dest] == 100;
        assert gasUsed > 0;
        assert token.balances[dest] == 100;
        assert token.totalAmount == 100;
        assert token.balance == 20;        
    }

    /**
     *  Transfer some tokens from an account to another.
     *
     *  @param  from    Source Address.
     *  @param  to      Target Address.
     *  @param  amount  The amount to be transfered from `from` to `to`.
     *  @param  msg     The `msg` content.
     *  @param  gas     The gas allocated to the execution.
     *  @returns        The gas left after executing the call.
     */
    method test_transfer(token:Token)
    {
        var src := new UserAccount(5);
        var dest := new UserAccount(10);
        var gasUsed := token.transfer(src, dest, 100, Msg(src, 0), 100);
        
    }
    
    method test_totalAmount()
    {
        var sender := new UserAccount(10); 
        var msg := Msg(sender, 10);
        var token := new Token(msg);
        var prevTotal := token.totalAmount;

        // totalAmount increment accordingly when new tokens are minted
        var dest := new UserAccount(10);
        var gasUsed := token.mint(dest, 100, Msg(sender, 10), 100);
        var curTotal := token.totalAmount;
        assert curTotal == prevTotal + 100;
        prevTotal := curTotal;


        // a second time minting
        var dest' := new UserAccount(5);
        var gasUsed' := token.mint(dest', 10, Msg(sender, 10), 100);
        curTotal := token.totalAmount;
        assert curTotal == prevTotal + 10;
        prevTotal := curTotal;


        // totalAmount remains unchanged when transfer is called
        assume dest in token.balances;
        assume dest' in token.balances;
        assume token.balances[dest] > 10;
        assume token.balances[dest'] == 10;
        var g := token.transfer(dest, dest', 10, Msg(dest, 0), 5);
        curTotal := token.totalAmount;
        assert curTotal == prevTotal;

    }

    method test_inv()
    {
        var sender := new UserAccount(10);
        var token := new Token(Msg(sender,0));

        var acc2 := new UserAccount(5);
        token.totalAmount := 0;
        token.balances := map[];
        assert token.GInv();

        token.totalAmount := 0;
        token.balances := map[sender := 0];
        assert token.GInv();

        token.totalAmount := 0;
        token.balances := map[sender := 1];
        assert !token.GInv();

        token.totalAmount := 10;
        token.balances := map[sender := 10];
        assert token.GInv();

        token.totalAmount := 10;
        token.balances := map[sender := 0];
        assert !token.GInv();

        token.totalAmount := 10;
        token.balances := map[sender := 5, acc2 := 5];
        assert token.GInv();

        token.totalAmount := 10;
        token.balances := map[sender := 5, acc2 := 8];
        assert !token.GInv();
        
        token.totalAmount := 10;
        token.balances := map[sender := 11];
        assert !token.GInv();

    }


}
