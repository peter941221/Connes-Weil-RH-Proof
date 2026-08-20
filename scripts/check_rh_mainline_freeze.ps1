[CmdletBinding()]
param(
    [switch]$AllowFrozen
)

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent (Split-Path -Parent $PSCommandPath)
Set-Location -LiteralPath $repoRoot

$freezePath = Join-Path $repoRoot 'RH_MAINLINE_FREEZE.md'
$activeRoot = 'normalizedSelectedFinalRouteDetectorCriterionCoverageRoot'

if (-not (Test-Path -LiteralPath $freezePath)) {
    throw "Missing RH mainline freeze manifest: $freezePath"
}

$freezeText = Get-Content -LiteralPath $freezePath -Raw
if ($freezeText -notlike "*$activeRoot*") {
    throw "Freeze manifest does not name the active RH root: $activeRoot"
}

$frozenPathPattern = '^(ConnesWeilRH/Dev/.*(Gate3U|RouteA|RawRenewal|LaneR).*)$|^(docs/proofs/.*gate3u.*)$'
$statusLines = @(git status --short)
$violations = @()

foreach ($line in $statusLines) {
    if ([string]::IsNullOrWhiteSpace($line)) {
        continue
    }

    $pathText = $line.Substring([Math]::Min(3, $line.Length)).Trim()
    $candidatePaths = @($pathText)
    if ($pathText -match ' -> ') {
        $candidatePaths = $pathText -split ' -> '
    }

    foreach ($candidate in $candidatePaths) {
        $path = $candidate.Trim().Trim('"')
        if (-not $AllowFrozen -and $path -match $frozenPathPattern) {
            $violations += $path
        }
    }
}

if ($violations.Count -gt 0) {
    $joined = $violations -join [Environment]::NewLine
    throw "Frozen side-route changes detected. Advance the RH mainline or pass -AllowFrozen for an explicitly reviewed archival edit:`n$joined"
}

Write-Output "RH mainline freeze check passed: active root $activeRoot"
if ($AllowFrozen) {
    Write-Output 'Explicit archival override: -AllowFrozen'
}
