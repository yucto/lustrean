{
  description = "2LTT";
  
  inputs = {
    nixpkgs.url = "github:jthulhu/nixpkgs/update/lean4";
    utils.url = "github:numtide/flake-utils";
  };
  
  outputs = { nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            lean4
            elan
          ];
        };
    });
}
