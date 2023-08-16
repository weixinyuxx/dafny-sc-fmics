include "../utils/NonNativeTypes.dfy"

module test_GInv_Provability {
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


    predicate GInv(totalAmount:nat, balances:map<Address, uint256>) {
        totalAmount == sum(balances)
    }

    lemma test_provability_1(totalAmount:nat, balances:map<Address, uint256>)
        requires balances == map[]
        requires totalAmount == 0
        ensures GInv(totalAmount, balances)
    {}

    lemma test_provability_2(totalAmount:nat, balances:map<Address, uint256>)
        requires balances == map[Account(100, false) := 10]
        requires totalAmount == 10
        ensures GInv(totalAmount, balances)
    {
        assert mapSum(balances) == mapSum(map[]) + 10;
    }

    lemma test_provability_3(totalAmount:nat, balances:map<Address, uint256>)
        requires balances == map[Account(100, false) := 10, Account(50, false) := 10]
        requires totalAmount == 20
        ensures GInv(totalAmount, balances)
    {
        // assert Account(100, false) in balances.Keys;
        // assert map[Account(50, false) := 10] == map key | key in balances.Keys && key != Account(100, false) :: balances[Account(100, false)];
        assert mapSum(balances) == mapSum(map[Account(50, false) := 10]) + 10;
        // assert balances[Account(100, false)] + balances[Account(50, false)] == 20;
        // assert mapSum(balances) == 20;
    }

    lemma test_provability_4(totalAmount:nat, balances:map<Address, uint256>)
        requires balances == map[Account(100, false) := 10, Account(50, false) := 20]
        requires totalAmount == 30
        ensures GInv(totalAmount, balances)
    {
        // the test is intended to show that when map[Account(100, false) := 10, Account(50, false) := 20], and totalAmount == 30
        // GInv is going to hold

        // guideline 1,2: both fails

        // guideline 3: to prove: sum(Account(100, false) := 10, Account(50, false) := 20) == 30, but it does not relate to any complex data type / expression, so no need to assert it (although one certainly can)
        // think about why this should be true:
        // either of the following way will lead to a passing proof, where the first one requires more insight, and the second one takes more advange of Dafny
        
        //  1. recursive perspective: main part of 3, combining 3a
        // guideline 3: think about the relationship between the map map[Account(100, false) := 10, Account(50, false) := 20] we have and the sum of it
        //              from a recursive perspective, we take the element out one at a time
        // guideline 3a: this includes manipulatin of maps
        assert mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10; // !!!: this line is mentioned later, come back when appropriate

        assert sum(balances) == sum(map[Account(50, false) := 20]) + 10;
        // guideline 4a: different from the case in test_correctness_2, the assertion with sum function fails
        //               since the GInv is indeed established assuming this assertion is true, the remaining work is to prove this assertion
        // guideline 3d: dig into the sum function in this assertion, the goal is then to prove: mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10;
        // one either tries to assert this directly, or find that this already includes a witness for a (guideline 3d(ii)), and then asserts it (it should appear before the previously failing assertion)
        // the proof then passes

        // 2. dig into Dafny
        // guideline 3d: dig into sum function, the goal is then to prove: mapSum(Account(100, false) := 10, Account(50, false) := 20) == 30
        // guideline 3d(ii): dig into mapSum function, find a witness for a = Account(100, false), and assert the statement where it is used
        assert mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10;

    }
}