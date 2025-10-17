// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
 
import {IPoolManager} from "@uniswap/v4-core/src/interfaces/IPoolManager.sol";
import {PoolKey} from "@uniswap/v4-core/src/types/PoolKey.sol";
import {SwapParams} from "@uniswap/v4-core/src/types/PoolOperation.sol";
import {TickMath} from "@uniswap/v4-core/src/libraries/TickMath.sol";
import {BalanceDelta, BalanceDeltaLibrary} from "@uniswap/v4-core/src/types/BalanceDelta.sol";
import {IUnlockCallback} from "@uniswap/v4-core/src/interfaces/callback/IUnlockCallback.sol";
import {Currency, CurrencyLibrary} from "@uniswap/v4-core/src/types/Currency.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {SafeCast} from "@uniswap/v4-core/src/libraries/SafeCast.sol";

contract Interactor is IUnlockCallback {
    using SafeERC20 for IERC20;
    using SafeCast for int128;
    using SafeCast for uint128;
    using SafeCast for int256;
    using BalanceDeltaLibrary for BalanceDelta;
    using CurrencyLibrary for Currency;
 
    IPoolManager public poolManager;
 
    struct SwapExactInputSingleHop {
        PoolKey poolKey;
        bool zeroForOne;
        uint128 amountIn;
        uint128 amountOutMin;
    }
 
    modifier onlyPoolManager() {
        require(msg.sender == address(poolManager), "not pool manager");
        _;
    }
 
    constructor(address _poolManager) {
        poolManager = IPoolManager(_poolManager);
    }
 
    receive() external payable {}
 
    function unlockCallback(bytes calldata data)
        external
        onlyPoolManager
        returns (bytes memory)
    {
        (address msgSender, SwapExactInputSingleHop memory params) =
            abi.decode(data, (address, SwapExactInputSingleHop));

        BalanceDelta delta = poolManager.swap({
            key: params.poolKey,
            params: SwapParams({
                zeroForOne: params.zeroForOne,

                amountSpecified: -(params.amountIn.toInt256()),

                sqrtPriceLimitX96: params.zeroForOne
                    ? TickMath.MIN_SQRT_PRICE + 1
                    : TickMath.MAX_SQRT_PRICE - 1
            }),
            hookData: ""
        });

        int128 amount0 = delta.amount0();
        int128 amount1 = delta.amount1();

        (
            Currency currencyIn,
            Currency currencyOut,
            uint256 amountIn,
            uint256 amountOut
        ) = params.zeroForOne
            ? (
                params.poolKey.currency0,
                params.poolKey.currency1,
                uint128(-amount0) == 0 ? 0 : uint256(uint128(-amount0)),
                uint128(amount1) == 0 ? 0 : uint256(uint128(amount1))
            )
            : (
                params.poolKey.currency1,
                params.poolKey.currency0,
                uint128(-amount1) == 0 ? 0 : uint256(uint128(-amount1)),
                uint128(amount0) == 0 ? 0 : uint256(uint128(amount0))
            );

        require(amountOut >= params.amountOutMin, "amount out < min");

        poolManager.take({
            currency: currencyOut,
            to: msgSender,
            amount: amountOut
        });

        poolManager.sync(currencyIn);

        address unwrappedCurrencyIn = Currency.unwrap(currencyIn);
        if (unwrappedCurrencyIn == address(0)) {
            poolManager.settle{value: amountIn}();
        } else {
            IERC20(unwrappedCurrencyIn).safeTransfer(address(poolManager), amountIn);
            poolManager.settle();
        }

        return "";
    }
 
    function swap(SwapExactInputSingleHop calldata params) external payable {
        Currency currencyIn = params.zeroForOne
            ? params.poolKey.currency0
            : params.poolKey.currency1;

        address unwrappedCurrencyIn = Currency.unwrap(currencyIn);
        
        if (unwrappedCurrencyIn != address(0)) {
            IERC20(unwrappedCurrencyIn).safeTransferFrom(msg.sender, address(this), params.amountIn);
        }
        
        poolManager.unlock(abi.encode(msg.sender, params));

        uint256 bal = currencyIn.balanceOf(address(this));
        if (bal > 0) {
            if (unwrappedCurrencyIn == address(0)) {
                (bool success, ) = msg.sender.call{value: bal}("");
                require(success, "refund failed");
            } else {
                IERC20(unwrappedCurrencyIn).safeTransfer(msg.sender, bal);
            }
        }
    }
}