use vstd::prelude::*;
use vstd::atomic::*;
use vstd::simple_pptr::*;
use vstd::invariant::*;
use vstd::logatom::AtomicUpdate;

verus! {


fn main() {
    {
        let (patomic, Tracked(perm)) = APAtomicU64::new(4);
        assert(perm.view().value == 4);
        assert(perm.view().patomic == patomic.id());
        
        // some operation 
        let (v, Tracked(perm)) = patomic.fetch_add_wrapping_original(Tracked(perm), 2);
        assert(v == 4);

        assert(perm.view().value == 6);
        assert(perm.view().patomic == patomic.id());

        let (v2, Tracked(perm)) = patomic.fetch_add_wrapping_original(Tracked(perm), 3);
        assert(v2 == 6);

        assert(perm.view().value == 9);
        assert(perm.view().patomic == patomic.id());
    }
    
    {
        let (patomic, Tracked(perm)) = APAtomicU64::new(4);
        
        // let (v, perm) = patomic.fetch_add_wrapping(2) atomically { update =>
        //   let (v, perm) = update(perm);
        //   (v, perm)
        // };

            /* (internal) */ let tracked input_perm = perm;
            
            /* before atomic */ /* check PRIVATE PRE */
            /* before atomic */ assert(true);
        let (v, Tracked(output_perm)) = patomic.fetch_add_wrapping(2, /* ) */

            /* (internal) */ Tracked(AtomicUpdate::<APermissionU64, APermissionU64>::assume_new()),
            /* (internal) */ Tracked(input_perm));
    
            /* atomic */ {
            /* atomic */ /* check ATOMIC PRE */
            /* atomic */ /* (internal) */ assert(patomic.id() == input_perm.view().patomic);
            /* atomic */ 
            /* atomic */ // atomic action happens

            /* atomic */ /* obtain ATOMIC POST */
            /* atomic */ /* (internal) */ assume(output_perm.view().patomic == input_perm.view().patomic);
            /* atomic */ /* (internal) */ assume(output_perm.view().value == wrapping_add_u64(input_perm.view().value as int, 2 as int));
            /* atomic */ }

            /* after atomic */ /* obtain PRIVATE POST */
            /* after atomic */ /* (internal) */ assume(v == input_perm.view().value);
            /* after atomic */ let tracked perm = output_perm;
        // ------------------------------------------------------------------------------------     
        
        assert(v == 4);

        assert(perm.view().value == 6);
        assert(perm.view().patomic == patomic.id());
    }
}

}