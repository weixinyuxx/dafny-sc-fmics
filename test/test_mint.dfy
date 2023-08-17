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

    predicate pre_mint(to:Address, amount:uint256, minter:Address, msg:Msg, gas:nat, balances:map<Address, uint256>, totalAmount:nat) {
        && msg.sender == minter
        && gas >= 1
        && (to !in balances ||  balances[to] as nat + amount as nat <= MAX_UINT256)
        && GInv(totalAmount, balances)
    }

    predicate post_mint(to:Address, amount:uint256, minter:Address, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat) {
        && totalAmount' == (totalAmount) + amount as nat
        && GInv(totalAmount', balances')
    }

    lemma test_pre_mint_usefulness(to:Address, amount:uint256, minter:Address, msg:Msg, gas:nat, balances:map<Address, uint256>, totalAmount:nat)
        requires minter == Account(100, false)
        requires msg.sender == minter
        requires gas == 1
        requires amount as nat == MAX_UINT256
        requires to !in balances
        requires GInv(totalAmount, balances)
        ensures pre_mint(to, amount, minter, msg, gas, balances, totalAmount)
    {}

    lemma test_pre_mint_provability(to:Address, amount:uint256, minter:Address, msg:Msg, gas:nat, balances:map<Address, uint256>, totalAmount:nat)
        requires gas == 0 || msg.sender != minter
        ensures !pre_mint(to, amount, minter, msg, gas, balances, totalAmount)
    {}

    lemma test_post_mint_correctness(to:Address, amount:uint256, minter:Address, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires to == Account(100, false)
        requires balances == map[]
        requires amount == 100
        requires balances' == map[Account(50, false) := 100]
        requires pre_mint(to, amount, minter, msg, gas, balances, totalAmount)
        ensures !post_mint(to, amount, minter, msg, gas, gas', balances, balances', totalAmount, totalAmount')
    {
        assert to !in balances';
        // not able to prove ==> look at the specification ==> confident that this is a bug
    }

    lemma test_post_mint_provability(to:Address, amount:uint256, minter:Address, msg:Msg, gas:nat, gas':nat, balances:map<Address, uint256>, balances':map<Address, uint256>, totalAmount:nat, totalAmount':nat)
        requires to == Account(100, false)
        requires balances == map[]
        requires totalAmount == 0
        requires amount == 100
        requires balances' == map[Account(100, false) := 100]
        requires totalAmount' == 100;
        requires minter == msg.sender
        requires gas == 1
        ensures pre_mint(to, amount, minter, msg, gas, balances, totalAmount)
        ensures post_mint(to, amount, minter, msg, gas, gas', balances, balances', totalAmount, totalAmount')
    {}



}