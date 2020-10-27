{
  pkgs ? (import ../../nix {}),
}:

pkgs.runCommand "FIR-compiler" { buildInputs = [ pkgs.zip ]; src = ./code; } ''
  mkdir -p $out
  cd $src
  zip -r $out/compiler.zip .
''
