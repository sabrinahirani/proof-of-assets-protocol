// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2Verifier {
    uint256 internal constant    PROOF_LEN_CPTR = 0x44;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x0f04;
    uint256 internal constant     INSTANCE_CPTR = 0x0f24;

    uint256 internal constant FIRST_QUOTIENT_X_CPTR = 0x05e4;
    uint256 internal constant  LAST_QUOTIENT_X_CPTR = 0x06a4;

    uint256 internal constant                VK_MPTR = 0x07c0;
    uint256 internal constant         VK_DIGEST_MPTR = 0x07c0;
    uint256 internal constant                 K_MPTR = 0x07e0;
    uint256 internal constant             N_INV_MPTR = 0x0800;
    uint256 internal constant             OMEGA_MPTR = 0x0820;
    uint256 internal constant         OMEGA_INV_MPTR = 0x0840;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x0860;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x0880;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x08a0;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x08c0;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x08e0;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x0900;
    uint256 internal constant              G1_X_MPTR = 0x0920;
    uint256 internal constant              G1_Y_MPTR = 0x0940;
    uint256 internal constant            G2_X_1_MPTR = 0x0960;
    uint256 internal constant            G2_X_2_MPTR = 0x0980;
    uint256 internal constant            G2_Y_1_MPTR = 0x09a0;
    uint256 internal constant            G2_Y_2_MPTR = 0x09c0;
    uint256 internal constant      NEG_S_G2_X_1_MPTR = 0x09e0;
    uint256 internal constant      NEG_S_G2_X_2_MPTR = 0x0a00;
    uint256 internal constant      NEG_S_G2_Y_1_MPTR = 0x0a20;
    uint256 internal constant      NEG_S_G2_Y_2_MPTR = 0x0a40;

    uint256 internal constant CHALLENGE_MPTR = 0x1120;

    uint256 internal constant THETA_MPTR = 0x1120;
    uint256 internal constant  BETA_MPTR = 0x1140;
    uint256 internal constant GAMMA_MPTR = 0x1160;
    uint256 internal constant     Y_MPTR = 0x1180;
    uint256 internal constant     X_MPTR = 0x11a0;
    uint256 internal constant  ZETA_MPTR = 0x11c0;
    uint256 internal constant    NU_MPTR = 0x11e0;
    uint256 internal constant    MU_MPTR = 0x1200;

    uint256 internal constant       ACC_LHS_X_MPTR = 0x1220;
    uint256 internal constant       ACC_LHS_Y_MPTR = 0x1240;
    uint256 internal constant       ACC_RHS_X_MPTR = 0x1260;
    uint256 internal constant       ACC_RHS_Y_MPTR = 0x1280;
    uint256 internal constant             X_N_MPTR = 0x12a0;
    uint256 internal constant X_N_MINUS_1_INV_MPTR = 0x12c0;
    uint256 internal constant          L_LAST_MPTR = 0x12e0;
    uint256 internal constant         L_BLIND_MPTR = 0x1300;
    uint256 internal constant             L_0_MPTR = 0x1320;
    uint256 internal constant   INSTANCE_EVAL_MPTR = 0x1340;
    uint256 internal constant   QUOTIENT_EVAL_MPTR = 0x1360;
    uint256 internal constant      QUOTIENT_X_MPTR = 0x1380;
    uint256 internal constant      QUOTIENT_Y_MPTR = 0x13a0;
    uint256 internal constant          R_EVAL_MPTR = 0x13c0;
    uint256 internal constant   PAIRING_LHS_X_MPTR = 0x13e0;
    uint256 internal constant   PAIRING_LHS_Y_MPTR = 0x1400;
    uint256 internal constant   PAIRING_RHS_X_MPTR = 0x1420;
    uint256 internal constant   PAIRING_RHS_Y_MPTR = 0x1440;

    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        assembly {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr, q) -> ret0, ret1, ret2 {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, q))
                ret0 := and(ret0, lt(y, q))
                ret0 := and(ret0, eq(mulmod(y, y, q), addmod(mulmod(x, mulmod(x, x, q), q), 3, q)))
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr, r) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end, r) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), r)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(r, 2))
                mstore(add(gp_mptr, 0xa0), r)
                ret := and(success, staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20))
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for
                    {}
                    lt(second_mptr, mptr)
                    {}
                {
                    let inv := mulmod(all_inv, mload(gp_mptr), r)
                    all_inv := mulmod(all_inv, mload(mptr), r)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), r)
                let inv_second := mulmod(all_inv, mload(first_mptr), r)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(success, staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40))
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40))
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(success, staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40))
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40))
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(G2_X_1_MPTR))
                mstore(0x60, mload(G2_X_2_MPTR))
                mstore(0x80, mload(G2_Y_1_MPTR))
                mstore(0xa0, mload(G2_Y_2_MPTR))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(NEG_S_G2_X_1_MPTR))
                mstore(0x120, mload(NEG_S_G2_X_2_MPTR))
                mstore(0x140, mload(NEG_S_G2_Y_1_MPTR))
                mstore(0x160, mload(NEG_S_G2_Y_2_MPTR))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let q := 21888242871839275222246405745257275088696311157297823662689037894645226208583 // BN254 base field
            let r := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field

            // Initialize success as true
            let success := true

            {
                // Load vk into memory
                mstore(0x07c0, 0x03b0d3e7025ca083f9e549982422d10885fb4e81033a551319b62f76813ae98c) // vk_digest
                mstore(0x07e0, 0x0000000000000000000000000000000000000000000000000000000000000014) // k
                mstore(0x0800, 0x30644b6c9c4a72169e4daa317d25f04512ae15c53b34e8f5acd8e155d0a6c101) // n_inv
                mstore(0x0820, 0x2a14464f1ff42de3856402b62520e670745e39fada049d5b2f0e1e3182673378) // omega
                mstore(0x0840, 0x220db0d8bf832baf9eecbf4fa49947e0b2a3d31df0a733ea5ae8abbdab442d5f) // omega_inv
                mstore(0x0860, 0x1d70265fc2e33776f0609a8b65dc22789d415875873f53a4a63e7d88ff30707f) // omega_inv_to_l
                mstore(0x0880, 0x000000000000000000000000000000000000000000000000000000000000003c) // num_instances
                mstore(0x08a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
                mstore(0x08c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
                mstore(0x08e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
                mstore(0x0900, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
                mstore(0x0920, 0x0000000000000000000000000000000000000000000000000000000000000001) // g1_x
                mstore(0x0940, 0x0000000000000000000000000000000000000000000000000000000000000002) // g1_y
                mstore(0x0960, 0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2) // g2_x_1
                mstore(0x0980, 0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed) // g2_x_2
                mstore(0x09a0, 0x090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b) // g2_y_1
                mstore(0x09c0, 0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa) // g2_y_2
                mstore(0x09e0, 0x186282957db913abd99f91db59fe69922e95040603ef44c0bd7aa3adeef8f5ac) // neg_s_g2_x_1
                mstore(0x0a00, 0x17944351223333f260ddc3b4af45191b856689eda9eab5cbcddbbe570ce860d2) // neg_s_g2_x_2
                mstore(0x0a20, 0x06d971ff4a7467c3ec596ed6efc674572e32fd6f52b721f97e35b0b3d3546753) // neg_s_g2_y_1
                mstore(0x0a40, 0x06ecdb9f9567f59ed2eee36e1e1d58797fd13cc97fafc2910f5e8a12f202fa9a) // neg_s_g2_y_2
                mstore(0x0a60, 0x1a4be647dce1fa9a53cb9615fb4e022a95fc6bbd22875b4359941b27aa417379) // fixed_comms[0].x
                mstore(0x0a80, 0x1d10107e3916d18b7ce3432b2ab5e2f81fe5af535f4a11830b890fd3f870d740) // fixed_comms[0].y
                mstore(0x0aa0, 0x05a21322f53fa6946f74e472bad9549baf1ea79fb6b02bf46aac430bec367bd3) // fixed_comms[1].x
                mstore(0x0ac0, 0x0b2310df32400c712b2992dbad69c1869351adbe6dd78940726fc817935151b0) // fixed_comms[1].y
                mstore(0x0ae0, 0x1329b4de3ea33a897e63c659f482f465126ea7a33c6d2b6efe1639452f1d4430) // fixed_comms[2].x
                mstore(0x0b00, 0x026f8e467a3f757dde9d322f9df0987c5bd7f4d5e146635f54435a75b4b04201) // fixed_comms[2].y
                mstore(0x0b20, 0x1afd4839b868941a8b1e83a7cc27249c0b6fc7848ec3d39d2cb1ecf94e415123) // fixed_comms[3].x
                mstore(0x0b40, 0x0cce80d82a839fbc46ac308271eb573a211cde808261e4a6de8003c285511cd2) // fixed_comms[3].y
                mstore(0x0b60, 0x026bbf6a96dd7b6caafbf079d66ce577cefb6010ce94a677d63edae288f36388) // fixed_comms[4].x
                mstore(0x0b80, 0x1faa9087e4abf37a27a3a4444d0c83a56d7e0644cfe2e6baa5bb7bf27c12eafa) // fixed_comms[4].y
                mstore(0x0ba0, 0x16df27143fac376469f1755f5bcd378baf6be1a92d5513a5a5edb514ece9d1ff) // fixed_comms[5].x
                mstore(0x0bc0, 0x27a30c33d688b167bcbafd9c2279b663d7e54e045f57e49c4c32ba7d696cd37c) // fixed_comms[5].y
                mstore(0x0be0, 0x0afa1edf96707ab4aa7d0b12e538fc0e220f3db7e3f66c1819eed449887a9e9a) // fixed_comms[6].x
                mstore(0x0c00, 0x285d41c95aee1699d5b669039bb768b53df54e0d1f4271b7ae5763b144d22f62) // fixed_comms[6].y
                mstore(0x0c20, 0x072a8715b5269e48bf189beef708390218e6ce9c9baf07c387a33b7ce3ab0625) // fixed_comms[7].x
                mstore(0x0c40, 0x10d399311c4689a488acbf4aab8a3f7cbbdf5e33b28a50d0305113aed809ae3a) // fixed_comms[7].y
                mstore(0x0c60, 0x1a87fc78f2eb1d5f1f60cba5fdc5eee83bc2b984f9484c8a2387d8739b3c836c) // fixed_comms[8].x
                mstore(0x0c80, 0x148132f617a20fd21fa4e61c71a7432519965e2ebbd8b61121b52dfd2150f59e) // fixed_comms[8].y
                mstore(0x0ca0, 0x128152dea41d9f1a8a64461825246ad9347b77cdb6d73c49d171bff1c785f844) // fixed_comms[9].x
                mstore(0x0cc0, 0x23c9be42e1beeee74b7af8950847678f24bddddd842c3a90071a8799266584fd) // fixed_comms[9].y
                mstore(0x0ce0, 0x0b20d0172e28d0866242f57dd2f5e572fcf5d0b6271ca860549d61c193f043f4) // fixed_comms[10].x
                mstore(0x0d00, 0x2da869e062961e84e081834480c022e386d7b769fc1c6259bc2ae0f99a013923) // fixed_comms[10].y
                mstore(0x0d20, 0x122cde1fa59fff33b4bce5793e441aaa68579bb1c4cf83957567c3f429589bdb) // fixed_comms[11].x
                mstore(0x0d40, 0x2ccfcc04b2e3d03702ff79140419be844f4a3b6f094a5a7ac84f414f145d3801) // fixed_comms[11].y
                mstore(0x0d60, 0x08b58459562950107332f95060f306f4d37f4c77ad1a6f0d3901eb6b327199f3) // fixed_comms[12].x
                mstore(0x0d80, 0x179dce6257340fb42d25112a50de0cb327474420441f9245b038174c933dd5d9) // fixed_comms[12].y
                mstore(0x0da0, 0x2f2e74978b97e64a2ab193a88ad6b62b629ec6c3f20dc7537c1fdc04de57fd42) // fixed_comms[13].x
                mstore(0x0dc0, 0x2a39d5edf416d81908281685d56625e2efb0ce2c522890e69de249e04be9182b) // fixed_comms[13].y
                mstore(0x0de0, 0x1951bc74360011881455f2bbca254163f15385dc250afe537cdddc7653cae094) // fixed_comms[14].x
                mstore(0x0e00, 0x1b2f44e2145f8dd493c21e7ae9f1057e56340fd69da98acda65b804a9af2e564) // fixed_comms[14].y
                mstore(0x0e20, 0x168069cbf12efb27a89fbc1bd08eb6016137243baba240652f854ebf617928e9) // fixed_comms[15].x
                mstore(0x0e40, 0x0d1d658febaf0f777dac19534482a6395434f87c79017ee51899e580190262a2) // fixed_comms[15].y
                mstore(0x0e60, 0x13f1ba837d58fd392460e602ddddc220b89b8a7d897693d997c83240810ec6f8) // fixed_comms[16].x
                mstore(0x0e80, 0x2ea58c7f08fde45ccf44df9fc6c4d9c98a0afefe91ef1be0975f371303e47815) // fixed_comms[16].y
                mstore(0x0ea0, 0x0e1252b99aac07818edc6165fa308fa5184e06187a3cccb0dba5798b492b948d) // fixed_comms[17].x
                mstore(0x0ec0, 0x1974c66aafb0ad456af44e18485aa89fac7df7440308b29a7eff8661dc386f20) // fixed_comms[17].y
                mstore(0x0ee0, 0x1a91333f97a1e5f9c7ef0b78c178fe51dacefcec4c3774500285ebc74c635081) // fixed_comms[18].x
                mstore(0x0f00, 0x0204c295a185b5d66c8d37c99cb0cf7ed43bd1f165fa036dcda54be52847c6c4) // fixed_comms[18].y
                mstore(0x0f20, 0x0e32dceac0238d4eb289a64b82f32b12e91324addccd20fc181ba090c065cdd1) // fixed_comms[19].x
                mstore(0x0f40, 0x21ad1ff8b68ec2fa46b6ffe59e3ff225b340d6bb63fa805ef385c9010d017448) // fixed_comms[19].y
                mstore(0x0f60, 0x24deb1e0e377b21f57e623cfb3e0d10b39e834f6b1752c19477422199dc50a77) // fixed_comms[20].x
                mstore(0x0f80, 0x0a7d80b78225e7b9389a63dbb3d93e6d0d4e336f5b87ddd4b071ed2f8901cfe2) // fixed_comms[20].y
                mstore(0x0fa0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[21].x
                mstore(0x0fc0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[21].y
                mstore(0x0fe0, 0x0e601f59825071f7335d419f9ac134d02806db2659bd89bf14c4486320709fb3) // permutation_comms[0].x
                mstore(0x1000, 0x1540d9849e10604327e8d82dc7c05223f1cbaf78a9bf900340ae2311fa8a91ba) // permutation_comms[0].y
                mstore(0x1020, 0x15784691540bf3e589a2c27b3e1bc553cb4a2c6da15fde2b2629fa3f393cc286) // permutation_comms[1].x
                mstore(0x1040, 0x26d41b857474fc8c805450d3b3eb893a7702ea17c4e87ff621039e04d601023e) // permutation_comms[1].y
                mstore(0x1060, 0x011662329d4ce99275f08418ad0d9be2408412337b51be993c9775e29c340cef) // permutation_comms[2].x
                mstore(0x1080, 0x07bc3715528d847e05c42f1e813e0bf1a9335d785e7e0717e737064e658463e2) // permutation_comms[2].y
                mstore(0x10a0, 0x0ce2ffc8a166077e987b03f84a2988cba6a4d9b26581422140ab4c8efff9a8af) // permutation_comms[3].x
                mstore(0x10c0, 0x1a8d0ef6a9bd23bdc21b53a709a47246a5b3a6937514d5418ef05b2e0feb52ac) // permutation_comms[3].y
                mstore(0x10e0, 0x174ce8183d29d5e6db69b49e8f12662183376fc36d6ef319a8f15676839c190f) // permutation_comms[4].x
                mstore(0x1100, 0x16f45c62a0c1a9c2434761b251a4157aad6852a491171a14dd751c737a8ed4ab) // permutation_comms[4].y

                // Check valid length of proof
                success := and(success, eq(0x0ea0, calldataload(PROOF_LEN_CPTR)))

                // Check valid length of instances
                let num_instances := mload(NUM_INSTANCES_MPTR)
                success := and(success, eq(num_instances, calldataload(NUM_INSTANCE_CPTR)))

                // Absorb vk diegst
                mstore(0x00, mload(VK_DIGEST_MPTR))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                let instance_cptr := INSTANCE_CPTR
                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := CHALLENGE_MPTR

                // Phase 1
                for
                    { let proof_cptr_end := add(proof_cptr, 0xc0) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 2
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0200) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)

                // Phase 3
                for
                    { let proof_cptr_end := add(proof_cptr, 0x02c0) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 4
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0100) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, 0x07a0) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W'

                // Read accumulator from instances
                if mload(HAS_ACCUMULATOR_MPTR) {
                    let num_limbs := mload(NUM_ACC_LIMBS_MPTR)
                    let num_limb_bits := mload(NUM_ACC_LIMB_BITS_MPTR)

                    let cptr := add(INSTANCE_CPTR, mul(mload(ACC_OFFSET_MPTR), 0x20))
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for
                        {
                            let cptr_end := add(cptr, mul(0x20, num_limbs))
                            let shift := num_limb_bits
                        }
                        lt(cptr, cptr_end)
                        {}
                    {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(lhs_y, shl(shift, calldataload(add(cptr, lhs_y_off))))
                        rhs_x := add(rhs_x, shl(shift, calldataload(add(cptr, rhs_x_off))))
                        rhs_y := add(rhs_y, shl(shift, calldataload(add(cptr, rhs_y_off))))
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(success, eq(mulmod(lhs_y, lhs_y, q), addmod(mulmod(lhs_x, mulmod(lhs_x, lhs_x, q), q), 3, q)))
                    success := and(success, eq(mulmod(rhs_y, rhs_y, q), addmod(mulmod(rhs_x, mulmod(rhs_x, rhs_x, q), q), 3, q)))

                    mstore(ACC_LHS_X_MPTR, lhs_x)
                    mstore(ACC_LHS_Y_MPTR, lhs_y)
                    mstore(ACC_RHS_X_MPTR, rhs_x)
                    mstore(ACC_RHS_Y_MPTR, rhs_y)
                }

                pop(q)
            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }

            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(K_MPTR)
                let x := mload(X_MPTR)
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                let mptr := X_N_MPTR
                let mptr_end := add(mptr, mul(0x20, add(mload(NUM_INSTANCES_MPTR), 6)))
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20), r)

                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for
                    { let l_i_cptr_end := add(X_N_MPTR, 0xc0) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := mulmod(mload(l_i_cptr), calldataload(INSTANCE_CPTR), r)
                let instance_cptr := add(INSTANCE_CPTR, 0x20)
                l_i_cptr := add(l_i_cptr, 0x20)
                for
                    { let instance_cptr_end := add(INSTANCE_CPTR, mul(0x20, mload(NUM_INSTANCES_MPTR))) }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0xc0))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let delta := 4131629893567559867359510883348571134090853742863529169391034518566172092834
                let y := mload(Y_MPTR)
                {
                    let f_18 := calldataload(0x09a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_18)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_18, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_0 := calldataload(0x06e4)
                    let a_1 := calldataload(0x0704)
                    let var7 := mulmod(a_0, a_1, r)
                    let a_2_prev_1 := calldataload(0x0744)
                    let var8 := addmod(var7, a_2_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_2, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := var11
                }
                {
                    let f_19 := calldataload(0x09c4)
                    let var0 := 0x2
                    let var1 := sub(r, f_19)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_19, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_1 := calldataload(0x0704)
                    let a_2_prev_1 := calldataload(0x0744)
                    let var7 := mulmod(a_1, a_2_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_2, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_20 := calldataload(0x09e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_20)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_20, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_1 := calldataload(0x0704)
                    let var7 := sub(r, a_1)
                    let var8 := addmod(a_2, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_18 := calldataload(0x09a4)
                    let var0 := 0x2
                    let var1 := sub(r, f_18)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_18, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_0 := calldataload(0x06e4)
                    let a_1 := calldataload(0x0704)
                    let var7 := addmod(a_0, a_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_2, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_20 := calldataload(0x09e4)
                    let var0 := 0x2
                    let var1 := sub(r, f_20)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_20, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_0 := calldataload(0x06e4)
                    let a_1 := calldataload(0x0704)
                    let var7 := mulmod(a_0, a_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_2, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_18 := calldataload(0x09a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_18)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_18, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_0 := calldataload(0x06e4)
                    let a_1 := calldataload(0x0704)
                    let var7 := sub(r, a_1)
                    let var8 := addmod(a_0, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_2, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_19 := calldataload(0x09c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_19)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_19, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_1 := calldataload(0x0704)
                    let a_2_prev_1 := calldataload(0x0744)
                    let var7 := addmod(a_1, a_2_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_2, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_19 := calldataload(0x09c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_19)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_19, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_2 := calldataload(0x0724)
                    let a_1 := calldataload(0x0704)
                    let var7 := sub(r, a_1)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_2, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_20 := calldataload(0x09e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_20)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_20, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_1 := calldataload(0x0704)
                    let var7 := mulmod(var6, a_1, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_21 := calldataload(0x0a04)
                    let a_1 := calldataload(0x0704)
                    let var0 := 0x1
                    let var1 := sub(r, var0)
                    let var2 := addmod(a_1, var1, r)
                    let var3 := mulmod(a_1, var2, r)
                    let var4 := mulmod(f_21, var3, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var4, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := addmod(l_0, sub(r, mulmod(l_0, calldataload(0x0ae4), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let perm_z_last := calldataload(0x0b44)
                    let eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(perm_z_last, perm_z_last, r), sub(r, perm_z_last), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x0b44), sub(r, calldataload(0x0b24)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0b04)
                    let rhs := calldataload(0x0ae4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x06e4), mulmod(beta, calldataload(0x0a44), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0704), mulmod(beta, calldataload(0x0a64), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0724), mulmod(beta, calldataload(0x0a84), r), r), gamma, r), r)
                    mstore(0x00, mulmod(beta, mload(X_MPTR), r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x06e4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0704), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0724), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0b64)
                    let rhs := calldataload(0x0b44)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0764), mulmod(beta, calldataload(0x0aa4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mulmod(beta, calldataload(0x0ac4), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0764), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mload(0x00), r), gamma, r), r)
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0b84), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0b84), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_2 := calldataload(0x07a4)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_10 := calldataload(0x08a4)
                        let var0 := 0x1
                        let var1 := mulmod(f_10, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := addmod(var8, var6, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var9, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0bc4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0ba4), sub(r, calldataload(0x0b84)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0be4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0be4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_3 := calldataload(0x07c4)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_3, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_11 := calldataload(0x08c4)
                        let var0 := 0x1
                        let var1 := mulmod(f_11, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := addmod(var8, var6, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var9, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0c24), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0c04), sub(r, calldataload(0x0be4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0c44), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0c44), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_4 := calldataload(0x07e4)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_4, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_12 := calldataload(0x08e4)
                        let var0 := 0x1
                        let var1 := mulmod(f_12, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := addmod(var8, var6, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var9, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0c84), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0c64), sub(r, calldataload(0x0c44)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0ca4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0ca4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_5 := calldataload(0x0804)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_5, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_13 := calldataload(0x0904)
                        let var0 := 0x1
                        let var1 := mulmod(f_13, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := 0x000000000000000000000000000000007fffffffffffffffffffffffffffffff
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0ce4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0cc4), sub(r, calldataload(0x0ca4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0d04), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0d04), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_6 := calldataload(0x0824)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_6, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_14 := calldataload(0x0924)
                        let var0 := 0x1
                        let var1 := mulmod(f_14, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := 0x000000000000000000000000000000007fffffffffffffffffffffffffffffff
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0d44), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0d24), sub(r, calldataload(0x0d04)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0d64), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0d64), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_7 := calldataload(0x0844)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_7, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_15 := calldataload(0x0944)
                        let var0 := 0x1
                        let var1 := mulmod(f_15, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := 0x30644e72e131a029b85045b68181585ca833e84879b9709143e1f593f0000001
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0da4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0d84), sub(r, calldataload(0x0d64)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0dc4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0dc4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_8 := calldataload(0x0864)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_8, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_16 := calldataload(0x0964)
                        let var0 := 0x1
                        let var1 := mulmod(f_16, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := 0x80
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0e04), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0de4), sub(r, calldataload(0x0dc4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0e24), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0e24), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0784)
                        let f_9 := calldataload(0x0884)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_9, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_17 := calldataload(0x0984)
                        let var0 := 0x1
                        let var1 := mulmod(f_17, var0, r)
                        let a_0 := calldataload(0x06e4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_1 := calldataload(0x0704)
                        let var8 := mulmod(var1, a_1, r)
                        let var9 := mulmod(var4, var0, r)
                        let var10 := addmod(var8, var9, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var10, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x0e64), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x0e44), sub(r, calldataload(0x0e24)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }

                pop(y)
                pop(delta)

                let quotient_eval := mulmod(quotient_eval_numer, mload(X_N_MINUS_1_INV_MPTR), r)
                mstore(QUOTIENT_EVAL_MPTR, quotient_eval)
            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(LAST_QUOTIENT_X_CPTR))
                mstore(0x20, calldataload(add(LAST_QUOTIENT_X_CPTR, 0x20)))
                let x_n := mload(X_N_MPTR)
                for
                    {
                        let cptr := sub(LAST_QUOTIENT_X_CPTR, 0x40)
                        let cptr_end := sub(FIRST_QUOTIENT_X_CPTR, 0x40)
                    }
                    lt(cptr_end, cptr)
                    {}
                {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(success, calldataload(cptr), calldataload(add(cptr, 0x20)))
                    cptr := sub(cptr, 0x40)
                }
                mstore(QUOTIENT_X_MPTR, mload(0x00))
                mstore(QUOTIENT_Y_MPTR, mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                {
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := mulmod(x, omega, r)
                    mstore(0x0360, x_pow_of_omega)
                    mstore(0x0340, x)
                    x_pow_of_omega := mulmod(x, omega_inv, r)
                    mstore(0x0320, x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    mstore(0x0300, x_pow_of_omega)
                }
                {
                    let mu := mload(MU_MPTR)
                    for
                        {
                            let mptr := 0x0380
                            let mptr_end := 0x0400
                            let point_mptr := 0x0300
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            point_mptr := add(point_mptr, 0x20)
                        }
                    {
                        mstore(mptr, addmod(mu, sub(r, mload(point_mptr)), r))
                    }
                    let s
                    s := mload(0x03c0)
                    mstore(0x0400, s)
                    let diff
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), r)
                    diff := mulmod(diff, mload(0x03e0), r)
                    mstore(0x0420, diff)
                    mstore(0x00, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03e0), r)
                    mstore(0x0440, diff)
                    diff := mload(0x03a0)
                    mstore(0x0460, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), r)
                    mstore(0x0480, diff)
                }
                {
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := 1
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0x20, coeff)
                }
                {
                    let point_1 := mload(0x0320)
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := addmod(point_1, sub(r, point_2), r)
                    coeff := mulmod(coeff, mload(0x03a0), r)
                    mstore(0x40, coeff)
                    coeff := addmod(point_2, sub(r, point_1), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0x60, coeff)
                }
                {
                    let point_0 := mload(0x0300)
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_0, sub(r, point_2), r)
                    coeff := mulmod(coeff, addmod(point_0, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x0380), r)
                    mstore(0x80, coeff)
                    coeff := addmod(point_2, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_2, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0xa0, coeff)
                    coeff := addmod(point_3, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_3, sub(r, point_2), r), r)
                    coeff := mulmod(coeff, mload(0x03e0), r)
                    mstore(0xc0, coeff)
                }
                {
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_2, sub(r, point_3), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0xe0, coeff)
                    coeff := addmod(point_3, sub(r, point_2), r)
                    coeff := mulmod(coeff, mload(0x03e0), r)
                    mstore(0x0100, coeff)
                }
                {
                    success := batch_invert(success, 0, 0x0120, r)
                    let diff_0_inv := mload(0x00)
                    mstore(0x0420, diff_0_inv)
                    for
                        {
                            let mptr := 0x0440
                            let mptr_end := 0x04a0
                        }
                        lt(mptr, mptr_end)
                        { mptr := add(mptr, 0x20) }
                    {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, r))
                    }
                }
                {
                    let coeff := mload(0x20)
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0a24), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, mload(QUOTIENT_EVAL_MPTR), r), r)
                    for
                        {
                            let mptr := 0x0ac4
                            let mptr_end := 0x0a24
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    for
                        {
                            let mptr := 0x0a04
                            let mptr_end := 0x0744
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0e64), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0e04), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0da4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0d44), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0ce4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0c84), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0c24), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0bc4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0704), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x06e4), r), r)
                    mstore(0x04a0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x0744), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x0724), r), r)
                    r_eval := mulmod(r_eval, mload(0x0440), r)
                    mstore(0x04c0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x0b24), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x0ae4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x0b04), r), r)
                    r_eval := mulmod(r_eval, mload(0x0460), r)
                    mstore(0x04e0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0e24), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0e44), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0dc4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0de4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0d64), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0d84), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0d04), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0d24), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0ca4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0cc4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0c44), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0c64), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0be4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0c04), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0b84), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0ba4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0b44), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0b64), r), r)
                    r_eval := mulmod(r_eval, mload(0x0480), r)
                    mstore(0x0500, r_eval)
                }
                {
                    let sum := mload(0x20)
                    mstore(0x0520, sum)
                }
                {
                    let sum := mload(0x40)
                    sum := addmod(sum, mload(0x60), r)
                    mstore(0x0540, sum)
                }
                {
                    let sum := mload(0x80)
                    sum := addmod(sum, mload(0xa0), r)
                    sum := addmod(sum, mload(0xc0), r)
                    mstore(0x0560, sum)
                }
                {
                    let sum := mload(0xe0)
                    sum := addmod(sum, mload(0x0100), r)
                    mstore(0x0580, sum)
                }
                {
                    for
                        {
                            let mptr := 0x00
                            let mptr_end := 0x80
                            let sum_mptr := 0x0520
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            sum_mptr := add(sum_mptr, 0x20)
                        }
                    {
                        mstore(mptr, mload(sum_mptr))
                    }
                    success := batch_invert(success, 0, 0x80, r)
                    let r_eval := mulmod(mload(0x60), mload(0x0500), r)
                    for
                        {
                            let sum_inv_mptr := 0x40
                            let sum_inv_mptr_end := 0x80
                            let r_eval_mptr := 0x04e0
                        }
                        lt(sum_inv_mptr, sum_inv_mptr_end)
                        {
                            sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                            r_eval_mptr := sub(r_eval_mptr, 0x20)
                        }
                    {
                        r_eval := mulmod(r_eval, mload(NU_MPTR), r)
                        r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), r), r)
                    }
                    mstore(R_EVAL_MPTR, r_eval)
                }
                {
                    let nu := mload(NU_MPTR)
                    mstore(0x00, calldataload(0x05a4))
                    mstore(0x20, calldataload(0x05c4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, mload(QUOTIENT_X_MPTR), mload(QUOTIENT_Y_MPTR))
                    for
                        {
                            let mptr := 0x10e0
                            let mptr_end := 0x0a20
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, mload(mptr), mload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x02e4
                            let mptr_end := 0xe4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0xa4), calldataload(0xc4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x64), calldataload(0x84))
                    mstore(0x80, calldataload(0xe4))
                    mstore(0xa0, calldataload(0x0104))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0440), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x0324))
                    mstore(0xa0, calldataload(0x0344))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0460), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x0564))
                    mstore(0xa0, calldataload(0x0584))
                    for
                        {
                            let mptr := 0x0524
                            let mptr_end := 0x0324
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0480), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, mload(G1_X_MPTR))
                    mstore(0xa0, mload(G1_Y_MPTR))
                    success := ec_mul_tmp(success, sub(r, mload(R_EVAL_MPTR)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x0e84))
                    mstore(0xa0, calldataload(0x0ea4))
                    success := ec_mul_tmp(success, sub(r, mload(0x0400)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x0ec4))
                    mstore(0xa0, calldataload(0x0ee4))
                    success := ec_mul_tmp(success, mload(MU_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                    mstore(PAIRING_LHS_Y_MPTR, mload(0x20))
                    mstore(PAIRING_RHS_X_MPTR, calldataload(0x0ec4))
                    mstore(PAIRING_RHS_Y_MPTR, calldataload(0x0ee4))
                }
            }

            // Random linear combine with accumulator
            if mload(HAS_ACCUMULATOR_MPTR) {
                mstore(0x00, mload(ACC_LHS_X_MPTR))
                mstore(0x20, mload(ACC_LHS_Y_MPTR))
                mstore(0x40, mload(ACC_RHS_X_MPTR))
                mstore(0x60, mload(ACC_RHS_Y_MPTR))
                mstore(0x80, mload(PAIRING_LHS_X_MPTR))
                mstore(0xa0, mload(PAIRING_LHS_Y_MPTR))
                mstore(0xc0, mload(PAIRING_RHS_X_MPTR))
                mstore(0xe0, mload(PAIRING_RHS_Y_MPTR))
                let challenge := mod(keccak256(0x00, 0x100), r)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_LHS_X_MPTR), mload(PAIRING_LHS_Y_MPTR))
                mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                mstore(PAIRING_LHS_Y_MPTR, mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(ACC_RHS_X_MPTR))
                mstore(0x20, mload(ACC_RHS_Y_MPTR))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_RHS_X_MPTR), mload(PAIRING_RHS_Y_MPTR))
                mstore(PAIRING_RHS_X_MPTR, mload(0x00))
                mstore(PAIRING_RHS_Y_MPTR, mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                mload(PAIRING_LHS_X_MPTR),
                mload(PAIRING_LHS_Y_MPTR),
                mload(PAIRING_RHS_X_MPTR),
                mload(PAIRING_RHS_Y_MPTR)
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}