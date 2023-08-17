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
        assert Account(100, false) in balances.Keys;
        assert map[Account(50, false) := 10] == map key | key in balances.Keys && key != Account(100, false) :: balances[Account(100, false)];
        assert mapSum(balances) == mapSum(map[Account(50, false) := 10]) + 10;
        assert mapSum(balances) == 20;
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
        
        //  1. manual insight: (guideline 3a)
        // guideline 3a: Find the property specific to the test input that is central to the answer why it leads to the conclusion you are trying to prove.
        // guideline 3ai: this includes manipulatin of maps
        assert mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10; // !!!: this line is mentioned later, come back when appropriate

        assert sum(balances) == sum(map[Account(50, false) := 20]) + 10;
        // guideline 4a: the assertion with sum function fails
        //               since the GInv is indeed established assuming this assertion is true, the remaining work is to prove this assertion
        // guideline 3b(i): dig into the sum function in this assertion, the goal is then to prove: mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10;
        // one asserts this directly, the proof then passes

        // The first way takes an inductive perspective of the problem, which is indeed not obvious. One can instead use the following way:
        // 2. dig into Dafny
        // guideline 3b(i): dig into sum function, the goal is then to prove: mapSum(Account(100, false) := 10, Account(50, false) := 20) == 30
        // guideline 3d(iv): dig into mapSum function, find a witness for a = Account(100, false)
        // Specifically, if it is the return value of a function, assert that the original invocation of the function does equal to the expression instantiated with the witness:
        assert mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10;

    }
}