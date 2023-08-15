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
        // assert map[] == map key | key in balances && key != Account(100, false) :: balances[key];
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
        assert map[Account(50, false) := 20] == map key | key in balances.Keys && key != Account(100, false) :: balances[key];
        assert mapSum(balances) == mapSum(map[Account(50, false) := 20]) + 10;
    }
}