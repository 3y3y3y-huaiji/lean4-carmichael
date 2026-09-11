<#
.SYNOPSIS
    LEAN 4 严格强制求值性能基准实测脚本 (中文版)
.DESCRIPTION
    使用 Lean 4 原生单调纳秒计时器 (IO.monoNanosNow)，在完全禁止惰性求值的严格模式下，
    实测计算反射 (Computational Reflection) 验证 561 极小性以及埃氏筛全量构建与遍历的真实纯计算耗时。
#>

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Write-Host "`n  ==========================================================================" -ForegroundColor Cyan
Write-Host "     LEAN 4 严格强制求值性能实测 (Strict Evaluation Benchmark)" -ForegroundColor Cyan
Write-Host "  ==========================================================================" -ForegroundColor Cyan
Write-Host "   说明: 将数组生成与 100% 内存遍历全部关进计时器内部，杜绝惰性求值优化偏差`n" -ForegroundColor DarkGray

$leanFile = "$PSScriptRoot\StrictBench.lean"
if (-not (Test-Path $leanFile)) {
    $leanFile = "$PWD\benchmark\StrictBench.lean"
}

Write-Host " [>] 正在通过 Lean 4 执行全量严格计算与纳秒级基准测试..." -ForegroundColor Yellow
lake env lean --run $leanFile

Write-Host "`n  ==========================================================================" -ForegroundColor Green
Write-Host "   ★ 严格基准测试测量完成！" -ForegroundColor Green
Write-Host "  ==========================================================================`n" -ForegroundColor Green