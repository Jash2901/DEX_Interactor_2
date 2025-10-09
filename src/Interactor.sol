// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IPoolManager} from "@uniswap/v4-core/src/interfaces/IPoolManager.sol";
import {PoolKey} from "@uniswap/v4-core/src/types/PoolKey.sol";
import {SwapParams} from "@uniswap/v4-core/src/types/PoolOperation.sol";
import {TickMath} from "@uniswap/v4-core/src/libraries/TickMath.sol";
import {ActionConstants} from "@uniswap/v4-periphery/libraries/ActionConstants.sol";
import {BalanceDelta, BalanceDeltaLibrary} from "@uniswap/v4-core/src/types/BalanceDelta.sol";
import {IUnlockCallback} from "@uniswap/v4-core/src/interfaces/callback/IUnlockCallback.sol";
import {Currency, CurrencyLibrary} from "@uniswap/v4-core/src/types/Currency.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";


contract Interactor is IUnlockCallback {
    
    using SafeERC20 for IERC20;
    using CurrencyLibrary for Currency;

    IPoolManager public poolManager;
    address private currentUser;

    constructor(address _poolManager) {
        poolManager = IPoolManager(_poolManager);
    }

    function swapExactInputSingle(
        PoolKey memory poolKey,
        bool zeroForOne,
        uint128 amountIn,
        uint128 amountOutMinimum
    ) external returns (uint128 amountOut) {
        if (amountIn == ActionConstants.OPEN_DELTA) {
            revert("OPEN_DELTA not supported");
        }

        currentUser = msg.sender;

        bytes memory data = abi.encode(poolKey, zeroForOne, amountIn, amountOutMinimum);
        bytes memory result = poolManager.unlock(data);

        currentUser = address(0);

        amountOut = abi.decode(result, (uint128));
    }

    function unlockCallback(bytes calldata data) external override returns (bytes memory) {
        require(msg.sender == address(poolManager), "Only poolManager");

        (
            PoolKey memory poolKey,
            bool zeroForOne,
            uint128 amountIn,
            uint128 amountOutMinimum
        ) = abi.decode(data, (PoolKey, bool, uint128, uint128));

        int256 amountSpecified = -int256(uint256(amountIn));
        uint160 sqrtPriceLimitX96 = zeroForOne
            ? TickMath.MIN_SQRT_PRICE + 1
            : TickMath.MAX_SQRT_PRICE - 1;

        SwapParams memory params = SwapParams({
            zeroForOne: zeroForOne,
            amountSpecified: amountSpecified,
            sqrtPriceLimitX96: sqrtPriceLimitX96
        });

        BalanceDelta delta = poolManager.swap(poolKey, params, bytes(""));

        int256 delta0 = BalanceDeltaLibrary.amount0(delta);
        int256 delta1 = BalanceDeltaLibrary.amount1(delta);

        // Settle debts
        if (delta0 < 0) {
            // Transfer tokens from user to PoolManager
            IERC20(Currency.unwrap(poolKey.currency0)).safeTransferFrom(
                currentUser,
                address(poolManager),
                uint256(-delta0)
            );
            // Sync the currency
            poolManager.sync(poolKey.currency0);
            // Mark as settled
            poolManager.settle();
        }
        
        if (delta1 < 0) {
            // Transfer tokens from user to PoolManager
            IERC20(Currency.unwrap(poolKey.currency1)).safeTransferFrom(
                currentUser,
                address(poolManager),
                uint256(-delta1)
            );
            poolManager.sync(poolKey.currency1);

            poolManager.settle();
        }

        if (delta0 > 0) {
            poolManager.take(poolKey.currency0, currentUser, uint256(delta0));
        }
        
        if (delta1 > 0) {
            poolManager.take(poolKey.currency1, currentUser, uint256(delta1));
        }

        uint128 amountOut = uint128(
            zeroForOne
                ? uint256(delta1) // Received token1
                : uint256(delta0) // Received token0
        );

        require(amountOut >= amountOutMinimum, "Too little received");

        return abi.encode(amountOut); 
    }
}