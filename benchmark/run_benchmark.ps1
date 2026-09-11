<#
.SYNOPSIS
    Lean 4 Strict Evaluation Benchmark Script (English Version)
.DESCRIPTION
    Uses Lean 4 native monotonic nanosecond clock (IO.monoNanosNow) under strict evaluation
    (no lazy evasion) to accurately profile the computation time of the Computational Reflection
    Carmichael bound check (N = 561) and large-scale Sieve of Eratosthenes construction & traversal.
#>

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Write-Host "`n  ==========================================================================" -ForegroundColor Cyan
Write-Host "     LEAN 4 Strict Evaluation Benchmark (Carmichael Reflection & Sieve)" -ForegroundColor Cyan
Write-Host "  ==========================================================================" -ForegroundColor Cyan
Write-Host "   Note: Array construction and 100% traversal are enclosed strictly within timers.`n" -ForegroundColor DarkGray

$leanFile = "$PSScriptRoot\StrictBench.lean"
if (-not (Test-Path $leanFile)) {
    $leanFile = "$PWD\benchmark\StrictBench.lean"
}

Write-Host " [>] Running strict execution and nanosecond profiling via Lean 4..." -ForegroundColor Yellow
lake env lean --run $leanFile

Write-Host "`n  ==========================================================================" -ForegroundColor Green
Write-Host "   * Strict Benchmark Finished Successfully!" -ForegroundColor Green
Write-Host "  ==========================================================================`n" -ForegroundColor Green