let _ = CmdLineParser.parse_cmdline [
  ("x64_poly1305", (fun win -> Vale_Poly1305_X64.va_code_Poly1305 win, Vale_Def_PossiblyMonad.ttrue), 4, false);
  ]
