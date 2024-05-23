#!/usr/bin/env perl
use strict;
use warnings;
use Path::Tiny;
use utf8;

my $prelude = <<'END_PRELUDE';
Require Export Lattice.All.
Require Export unscoped.

Module Type syntax_sig
  (Export lattice : Lattice).
END_PRELUDE

my $prologue = <<'END_PROLOGUE';

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.

Global Disable Notation "'var'" : subst_scope.
Global Disable Notation "↑".
Global Open Scope subst_scope.

End syntax_sig.
END_PROLOGUE

my $syntax_path = path('theories/Autosubst2/syntax.v');

my $syntax = join('',map { (my $s = $_) =~ s/^(Hint|Instance)/#[export]$1/; $s } grep(!/^Require Export/,$syntax_path->lines_utf8));

$syntax =~ s/\(\(fun \w+ => \(eq_refl\) \w+\) \w+\)/eq_refl/g;

$syntax_path->spew_utf8($prelude,$syntax,$prologue);
