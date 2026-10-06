# About

This is an external type checker for the [Lean 4](https://lean-lang.org/) programming language and theorem prover. You can read more about what an external type checker is and why you might want to use one in [this book](https://ammkrn.github.io/type_checking_in_lean4/).

# Usage

## Building and running the binary

Either run the binary directly through cargo `cargo +nightly-2026-07-30 run --release -- <path_to_config>`, or build the binary using `cargo +nightly-2026-07-30 build --release`, then run the built binary, passing a path to a [configuration](#configuration-file). Building with cargo should just work on all modern platforms without requiring additional build steps.

The binary takes a single argument, which is a path to a json configuration file describing the resource locations and desired options needed to run the type checker. Export files can be streamed via stdin rather than by file path by setting the configuration option `use_stdin: true`, at which point the executable will expect to receive the contents of the export file via stdin.

Export files can be created with [lean4export](https://github.com/leanprover/lean4export).

## Using the library

The library component can be imported and used as a normal rust crate by specifying it as a dependency in a `Cargo.toml` file.

# Configuration file

The execution conditions of `nanoda_bin` are determined by a json configuration file, there is no old school CLI. This was a conscious design choice to accommodate modern development practices (checking in to version control, use with CI and automation) and what we envision to be the most likely use case for external type checkers (running a suite of external checkers). The UI for external checkers is somewhat TBD and is expected to evolve as the community starts to integrate these into what they're doing.

Given that lean4export already uses json as its export format, adding a json parser as a dependency doesn't increase the overall complexity of the project.

## Configuration options

Users can either specify a path to the export file to be checked, or set `"use_stdin": true`, in which case the program will wait for the export file to be passed via stdin. If the `"export_file_path"` key is not defined, then `"use_stdin"` must be set to `true`. Specifying an export file and setting `"use_stdin": true` are mutually exclusive, and will result in a hard error.

The `"permitted_axioms"` list is where users specify the axioms an export file is permitted to use. For axioms to be permitted, they must be identified in the config file. The average Lean user will want to permit the three semi-official axioms, which are `Quot.sound`, `Classical.choice`, and `propext`, and most export files will also rely on `Lean.trustCompiler`.

if `"unpermitted_axiom_hard_error"` is set to `true`, the presence of an axiom in the export file that is not in the `permitted_axioms` list will cause a hard error and abort checking, regardless of whether it's used by any later declarations. If set to `false`, the unpermitted axiom will simply be ignored, meaning it will not be checked, will not be added to the environment, and will cause a hard error only if another exported declaration actually tries to use it. This value is currently set to `true` by default out of an abundance of caution, but this may change; most users will probably want to set this to `false`, since things like the prelude's `sorryAx` are declared so that they may be used by metaprograms, but will not actually be invoked by other declarations in the file and are therefore safe to just skip.

If `"unsafe_permit_all_axioms"` is set to `true`, all axioms will be admitted to the environment (when using this option, you must also explicitly set `"unpermitted_axiom_hard_error": false` to avoid a hard error on startup). This is checked so as to be mutually exclusive with any of the axiom allow list/whitelist features: it cannot be combined with `"unpermitted_axiom_hard_error": true` or with a non-empty `"permitted_axioms"` list, and either combination will result in a hard error. Defaults to `false`.

`"nat_extension"` and `"string_extension"` enable or disable the Nat and String kernel extensions. While we expect most users to opt into the Nat and String kernel extensions, they are disabled by default.

`"pp_declars"` is a list of declarations to be printed back by the pretty printer.

`"pp_options"` are the options to be used by the pretty printer.

`"pp_to_stdout"` determines whether the pretty printer output is written to stdout. This is not mutually exclusive with `"pp_output_path"`; if both options are set, the pretty printer output will be written to both stdout and the specified path.

`"pp_output_path"` can be set if the pretty printer output should be written to a file path. This is not mutually exclusive with `"pp_output_path"`; if both options are set, the pretty printer output will be written to both stdout and the specified path.

`"declar_sep"` is a separator to print between each pretty printed declaration. A default of "\n\n" will end each declaration with a newline, then put a blank line between successive declarations. While this does allow for the injection of arbitrary strings into the pretty printer output, it's rejected if not valid UTF-8, and the configuration file is controlled entirely by the operator of the type checker, so I don't consider this any more of a vector for attack than specifying an incorrect export file path or knowingly whitelisting an unsound axiom.

`"paired_export_file_path"`, see the next section.

If `"print_success_message"` is set to false, no additional output will be printed on success, and users should look to the platform-specific exit code. If `"pp_to_stdout"` is `true` and `"print_success_message"` is `false` the pretty printer output will still be written to stdout.

An example configuration file:

```
{
    "export_file_path": "MyLeanProject/export",
    "use_stdin": false,
    "permitted_axioms": [
        "propext",
        "Classical.choice",
        "Quot.sound",
        "Lean.trustCompiler"
    ],
    "unpermitted_axiom_hard_error": true,
    "nat_extension": true,
    "string_extension": true,
    "pp_declars": ["Nat.add_zero", "Eq.symm"],
    "pp_output_path": "/Users/user/file.txt",
    "pp_to_stdout": false,
    "pp_options": {
        "all": null,
        "explicit": false,
        "universes": null,
        "notation": null,
        "proofs": false,
        "indent": 2,
        "width": 100,
        "declar_sep": "\n\n",
    },
    "print_success_message": false
}
```

## Pairing declarations between given statement and proofs with unnamed declarations

With `paired_export_file_path` configuration, the last statement in the paired export file will be compared with the last one in the export file.

If the former one is syntactically equivalent to the latter one modulo renaming of inductive types, opaques, and axioms, then this declarations in the paired export file will be mapped into ones in the export file. A proofs derived from the paired export file with declarations renamed to the export file ones will be printed to stdout:

```bash
path/to/nanoda_bin config.json > adapted_solution_to_statement.json
```

. An example of `config.json` is as follows:

```json
{
    "export_file_path": "statement.ndjson",
    "paired_export_file_path": "solution.ndjson",
    "use_stdin": false,
    "permitted_axioms": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "unsafe_permit_all_axioms": false,
}
```

. The configuration `unpermitted_axiom_hard_error` should be set to false, and the statement should be exported as type of a custom axiom, which can be done with [a modified lean4export](https://github.com/WuProver/lean4export) in the lean project with the statement to be exported:

```bash
lake env path/to/lean4export StatementModule --as-axiom="statement" -- Nat Quot.mk Quot.lift Quot.ind String Bool Char List propext Classical.choice eagerReduce "statement" > statement.ndjson
```

where the 1st and 2nd `statement` is the name of the declaration whose type is the statement and value will not be exported, in module `StatementModule`. And solution `solution` defined in module `SolutionModule` can be exported by

```bash
lake env path/to/lean4export SolutionModule -- "solution" > solution.ndjson
```
.
