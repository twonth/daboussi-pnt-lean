param(
    [Parameter(Mandatory = $true)][string]$LeanBinary,
    [Parameter(Mandatory = $true)][string]$MathlibRoot
)
$ErrorActionPreference = 'Stop'
$root = $PSScriptRoot
$lib = Join-Path $root '.lake\build\lib\lean'
$logs = Join-Path $root 'Verification'
New-Item -ItemType Directory -Force $lib, $logs | Out-Null
$paths = @($lib, (Join-Path $MathlibRoot '.lake\build\lib\lean'))
$paths += Get-ChildItem (Join-Path $MathlibRoot '.lake\packages') -Directory | ForEach-Object {
    Join-Path $_.FullName '.lake\build\lib\lean'
}
$env:LEAN_PATH = $paths -join ';'
$modules = @(
    'Daboussi.Arithmetic',
    'Daboussi.Definitions',
    'Daboussi.Basic',
    'Daboussi.Balance',
    'Daboussi.Limsup',
    'Daboussi.BelowCutoff',
    'Daboussi.ExcessBootstrap',
    'Daboussi.Reduction',
    'Daboussi.IntegralRegularity',
    'Daboussi.BelowIntegral',
    'Daboussi.Steps',
    'Daboussi.SignedIntegral',
    'Daboussi.SmallValues',
    'Daboussi.GeometricAveraging',
    'Daboussi.Blocks',
    'Daboussi.SmoothSupport',
    'Daboussi.SmoothConvolution',
    'Daboussi.CoprimeCounting',
    'Daboussi.FloorBands',
    'Daboussi.SmoothHarmonic',
    'Daboussi.TailKernels',
    'Daboussi.SmoothMass',
    'Daboussi.SmoothIntegrability',
    'Daboussi.SmoothStepMass',
    'Daboussi.Comparison',
    'Daboussi.DeficitControl',
    'Daboussi.SmoothLogarithms',
    'Daboussi.ExcessRecurrence',
    'Daboussi.ExcessSupport',
    'Daboussi.ExcessFubini',
    'Daboussi.ExcessScaling',
    'Daboussi.ExcessMoment',
    'Daboussi.ThreeRanges',
    'Daboussi.MertensUpper',
    'Daboussi.MertensProduct',
    'Daboussi.MertensCoefficient',
    'Daboussi.ExcessEstimate',
    'Daboussi.Fundamental',
    'Daboussi', 'Proofs', 'Audit', 'Challenge', 'Solution', 'MainAudit'
)
Push-Location $root
try {
    & $LeanBinary --version | Set-Content (Join-Path $logs 'lean-version.txt') -Encoding utf8
    foreach ($module in $modules) {
        $relative = $module.Replace('.', '\')
        $output = Join-Path $lib "$relative.olean"
        New-Item -ItemType Directory -Force (Split-Path $output) | Out-Null
        $messages = & $LeanBinary -o $output "$relative.lean" 2>&1
        $code = $LASTEXITCODE
        if ($messages) {
            $messages | Set-Content (Join-Path $logs "$module.log") -Encoding utf8
        } else {
            'PASS: compiler exit code 0; no diagnostics.' | Set-Content (Join-Path $logs "$module.log") -Encoding utf8
        }
        if ($code -ne 0) { throw "Lean failed for $module; see Verification." }
        $challengePlaceholder = $module -eq 'Challenge'
        if (-not $challengePlaceholder -and (($messages | Out-String) -match 'sorryAx|declaration uses .sorry.|Lean\.ofReduceBool|Lean\.trustCompiler')) {
            throw "Unapproved proof dependency in completed component $module."
        }
        foreach ($message in $messages) {
            if ("$message" -match 'depends on axioms: \[([^\]]*)\]') {
                foreach ($axiom in ($Matches[1] -split ',')) {
                    if ($axiom.Trim() -notin @('propext', 'Classical.choice', 'Quot.sound')) {
                        throw "Unapproved axiom in $module : $axiom"
                    }
                }
            }
        }
        Write-Output "Checked $module"
    }
    Write-Output 'All source modules and axiom audits passed.'
} finally { Pop-Location }
