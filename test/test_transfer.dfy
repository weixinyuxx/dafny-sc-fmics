include "../utils/NonNativeTypes.dfy"

module test_GInv_Provability {
    import opened NonNativeTypes

    datatype Account = Account(balance:uint256, isContract:bool)
    datatype Msg = Msg(sender: Account, value: uint256) 


    type Address = Account

    function mapSum(m:map<Address, uint256>):nat
    {
        if |m| == 0 then 0 else
        var a :| a in m.Keys;
        var mapLess:map<Address, uint256> := map key | key in m.Keys && key != a :: m[key];
        m[a] as nat + mapSum(mapLess)
    }

    function sum(m: map<Address, uint256>): nat
        ensures m == map[] ==> sum(m) == 0
    {
        mapSum(m)
    }

    predicate GInv(totalAmount:nat, balances:map<Address, uint256>) {
        totalAmount == sum(balances)
    }

    predicate pre_transfer(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, balances:map<Address, uint256>, totalAmount:nat)
    {
        && from in balances
        && gas >= 1
        && msg.value == 0
        && balances[from] >= amount && msg.sender == from 
        && (to !in balances ||  balances[to] as nat + amount as nat <= MAX_UINT256)
        && msg.sender == from  
        && GInv(totalAmount, balances)
    }

    predicate post_transfer(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires pre_transfer(from, to, amount, msg, gas, balances, totalAmount)
    {
        && GInv(totalAmount', balances')
        && from in balances' && balances'[from] == (balances[from]) - amount
        && to in balances'
        && (to != from ==> balances'[to] >= amount)
        && (to == from ==> balances' == (balances))
        && gas' < gas
    }

    lemma test_pre_transfer_usefulness(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, balances:map<Address, uint256>, totalAmount:nat)
        requires from == Account(100, false)
        requires amount == 10
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        ensures pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
    {
        assert sum(map[Account(100, false) := 10]) == 10;
        assert balances[from] >= amount;
    }

    lemma test_pre_transfer_provability(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, balances:map<Address, uint256>, totalAmount:nat)
        requires from == Account(100, false)
        requires amount > 10
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        ensures !pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
    {}

    lemma test_post_transfer_correctness_1(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires from == Account(100, false)
        requires amount == 10
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        requires pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
        requires post_transfer(from, to, amount, msg, gas, gas', balances, balances', totalAmount, totalAmount')
        ensures totalAmount' == 10
    {
        assert sum(map[Account(100, false) := 10]) == 10;

        assert balances' == map[Account(100, false) := 0, to := 10];
        // not able to prove ==> look at the specification ==> find a counter example below
        
        assert mapSum(balances') == mapSum(map[to:=10]) + 0;
        assert sum(balances') == 10; 
    }

    lemma test_post_transfer_correctness_1_counterexample(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires from == Account(100, false)
        requires amount == 10
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        requires totalAmount' == 11
        requires to == Account(50, false)
        requires gas' == gas - 1
        requires balances' == map[Account(100, false) := 0, to := 10, Account(25, false):= 1]
        ensures pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
        ensures post_transfer(from, to, amount, msg, gas, gas', balances, balances', totalAmount, totalAmount')
    {
        assert sum(map[Account(100, false) := 10]) == 10;

        assert map[Account(100, false) := 0, to := 10, Account(25, false):= 1][Account(100, false)] == 0;
        assert Account(100, false) in balances';
        var mapLess:map<Address, uint256> := map key | key in balances'.Keys && key != Account(100, false) :: balances'[key];
        assert mapLess == map[to := 10, Account(25, false):= 1];
        assert mapSum(balances') == 0 + mapSum(map[to := 10, Account(25, false):= 1]);
        assert mapSum(map[to := 10, Account(25, false):= 1]) == 10 + mapSum(map[Account(25, false):= 1]);
        assert sum(balances') == 11; 
    }

    lemma test_post_transfer_correctness_2(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires from == Account(100, false)
        requires amount == 5
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        requires gas' != gas - 1
        ensures pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
        ensures !post_transfer(from, to, amount, msg, gas, gas', balances, balances', totalAmount, totalAmount')
    {
        assert sum(map[Account(100, false) := 10]) == 10;
        
        // not able to prove ==> see specification ==> directly find that it does not explicitly say that gas must -1
    }

    lemma test_post_transfer_correctness_3(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires from == Account(100, false)
        requires amount == 5
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        requires balances' != map[Account(100, false) := 5, to := 5]
        ensures pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
        ensures !post_transfer(from, to, amount, msg, gas, gas', balances, balances', totalAmount, totalAmount')
    {
        assert sum(map[Account(100, false) := 10]) == 10;
        // not able to prove ==> look at the specification ==> find a counter example below

    }

    lemma test_post_transfer_correctness_3_counterexample(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires from == Account(100, false)
        requires amount == 5
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        requires totalAmount' == 15
        requires to == Account(50, false)
        requires gas' == gas - 1
        requires balances' == map[Account(100, false) := 5, to := 5, Account(25, false):= 5]

        ensures pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
        ensures post_transfer(from, to, amount, msg, gas, gas', balances, balances', totalAmount, totalAmount')
    {
        assert sum(map[Account(100, false) := 10]) == 10;

        assert Account(100, false) in balances';
        var mapLess:map<Address, uint256> := map key | key in balances'.Keys && key != Account(100, false) :: balances'[key];
        assert mapLess == map[to := 5, Account(25, false):= 5];
        assert mapSum(balances') == 5 + mapSum(map[to := 5, Account(25, false):= 5]);
        assert mapSum(map[to := 5, Account(25, false):= 5]) == 5 + mapSum(map[Account(25, false):= 5]);
        assert sum(balances') == 15; 
    }

    lemma test_post_transfer_provability_1(from:Address, to:Address, amount:uint256, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires from == Account(100, false)
        requires amount == 5
        requires balances == map[Account(100, false) := 10]
        requires gas > 0
        requires msg.sender == from
        requires msg.value == 0
        requires totalAmount == 10
        requires totalAmount' == 10
        requires to == Account(50, false)
        requires gas' == gas - 1
        requires balances' == map[Account(100, false) := 5, to := 5]
        ensures pre_transfer(from, to, amount, msg, gas, balances,totalAmount)
        ensures post_transfer(from, to, amount, msg, gas, gas', balances, balances', totalAmount, totalAmount')
    {
        assert sum(map[Account(100, false) := 10]) == 10;
        assert mapSum(map[Account(100, false) := 5, to := 5]) == 5 + mapSum(map[to:=5]);
    }
}
