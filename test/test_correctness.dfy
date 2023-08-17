include "../utils/NonNativeTypes.dfy"

module test_GInv_Correctness {
    import opened NonNativeTypes

    datatype Account = Account(balance:uint256, isContract:bool)

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


    // function sum(m: map<Address, uint256>): nat
    //     ensures m == map[] ==> sum(m) == 0

    predicate GInv(totalAmount:nat, balances:map<Address, uint256>) {
        totalAmount == sum(balances)
    }

    lemma test_deterministic(totalAmount:nat, totalAmount':nat, balances:map<Address, uint256>)
        requires GInv(totalAmount, balances)
        requires GInv(totalAmount', balances)
        ensures totalAmount == totalAmount'
    {}

    lemma test_correctness_1(totalAmount:nat, balances:map<Address, uint256>)
        requires totalAmount != 0
        requires balances == map[]
        ensures !GInv(totalAmount, balances)
    {}

    lemma test_correctness_2(totalAmount:nat, balances:map<Address, uint256>)
        requires balances == map[Account(100, false) := 10]
        requires totalAmount != 10
        ensures !GInv(totalAmount, balances)
    {
        var m := map[Account(100, false) := 10];
        assert sum(m) == 10;
        // the test is intended to show that when balances == map[Account(100, false) := 10],
        // in order to have GInv established, the totalAmount cannot be anything other than 10

        // guideline 1,2: both fails

        //  1. manual insight: (guideline 3a)
        // guideline 3a: Find the property specific to the test input that is central to the answer why it leads to the conclusion you are trying to prove.
        // guideline 3ai: this includes manipulatin of maps
        assert sum(map[Account(100, false) := 10]) == 10;

        //  2. do not have insight, just dig into the predicate function
        // Digging into GInv, and replace it with the function and value it is invocating:
        assert sum(map[Account(100, false) := 10]) == 10;
    }

    // lemma test_correctness_3(totalAmount:nat, balances:map<Address, uint256>)
    //     requires exists v:uint256 | v in balances.Values :: v as nat > totalAmount
    //     ensures !GInv(totalAmount, balances)
    // {
    //     var v:uint256 :| v in balances.Values && v as nat > totalAmount;
    //     var k :| k in balances.Keys && balances[k] == v;
    //     assert v == balances[k];
    //     var mapLess:map<Address, uint256> := map key | key in balances.Keys && key != k :: balances[key];
    //     assert mapSum(balances) == balances[k] as nat + mapSum(mapLess) by {
    //         assert |balances| != 0;
    //         assert k in balances.Keys;
    //         assert mapLess == map key | key in balances.Keys && key != k :: balances[key];
    //     }
    // }

    lemma test_correctness_4(totalAmount:nat, balances:map<Address, uint256>)
        requires balances == map[Account(100, false) := 10, Account(50, false) := 10]
        requires totalAmount != 20
        ensures !GInv(totalAmount, balances)
    {
        assert mapSum(balances) == mapSum(map[Account(50, false) := 10]) + 10;
    }

    // lemma test_correctness_5(totalAmount:nat, balances:map<Address, uint256>)
    //     requires balances == map[Account(100, false) := 10, Account(100, false) := 10]
    //     requires totalAmount != 20
    //     ensures !GInv(totalAmount, balances)
    // // can two accounts have the same amount of gas in their account
    // // {}

    lemma test_correctness_6(totalAmount:nat, balances:map<Address, uint256>)
        requires balances == map[Account(100, false) := 10, Account(50, false) := 20]
        requires totalAmount != 30
        ensures !GInv(totalAmount, balances)
    {
        assert map[Account(50, false) := 20] == map key | key in balances.Keys && key != Account(100, false) :: balances[key];
        assert mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10;
    }

    // lemma test_correctness_7(totalAmount:nat, balances:map<Address, uint256>)
    //     requires balances == map[Account(100, false) := 10, Account(100, false) := 20]
    //     requires totalAmount != 30
    //     ensures !GInv(totalAmount, balances)
    // {}


// test axioms
    lemma test_add(m: map<Address, uint256>, k: Address, v: nat)
        requires sum(m) == 5
        requires v == 5
        requires (if k in m then m[k] else 0) as nat + v <= MAX_UINT256
        requires sum(m[k := ((if k in m then m[k] else 0) as nat + v) as uint256]) == 10
        ensures sum(m[k := ((if k in m then m[k] else 0) as nat + v) as uint256]) == sum(m) + v
    {}

}