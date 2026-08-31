[CmdletBinding()]
param(
    [switch]$AllowFrozen
)

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent (Split-Path -Parent $PSCommandPath)
Set-Location -LiteralPath $repoRoot

$freezePath = Join-Path $repoRoot 'RH_MAINLINE_FREEZE.md'
$auditSocket = 'normalizedSelectedFinalRouteDetectorCriterionCoverageRoot'
$activeRouteMarker = 'detector-specific semi-local positivity'

if (-not (Test-Path -LiteralPath $freezePath)) {
    throw "Missing RH mainline freeze manifest: $freezePath"
}

$freezeText = Get-Content -LiteralPath $freezePath -Raw
if ($freezeText -notlike "*$auditSocket*") {
    throw "Freeze manifest does not name the RH-equivalent audit socket: $auditSocket"
}
if ($freezeText -notlike "*$activeRouteMarker*") {
    throw "Freeze manifest does not name the healthy CompactLog mainline"
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

Write-Output "RH mainline freeze check passed: healthy CompactLog mainline; audit socket $auditSocket"
if ($AllowFrozen) {
    Write-Output 'Explicit archival override: -AllowFrozen'
}
