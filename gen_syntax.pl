#!/usr/bin/env perl
use strict;
use warnings;
use Path::Tiny;

my $prelude = <<'END_PRELUDE';
From mathcomp Require Export ssreflect.order.
From WR Require Export unscoped.

Module Type grade_sig.
Parameter grade : latticeType tt.
End grade_sig.

Module Type syntax_sig
  (Import grade : grade_sig).
END_PRELUDE

my $prologue = <<'END_PROLOGUE';
End syntax_sig.
END_PROLOGUE

my $syntax_path = path('syntax.v');

my $syntax = join('',map { (my $s = $_) =~ s/^(Hint|Instance)/#[export]$1/; $s } grep(!/^Require Export/,$syntax_path->lines_utf8));

$syntax_path->spew_utf8($prelude,$syntax,$prologue);
