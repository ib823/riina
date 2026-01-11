-- ═══════════════════════════════════════════════════════════════════════════════
-- TERAS ROOT PACKAGE
-- Track F/E Deliverable: Ada/SPARK Core
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- SPARK Status: PLATINUM
-- Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
--
-- This is the root package for all TERAS Ada/SPARK components.
-- All child packages inherit SPARK_Mode and verification requirements.

pragma SPARK_Mode (On);

package Teras
   with Pure,
        SPARK_Mode => On
is
   pragma Pure;

   --  TERAS version information
   Version_Major : constant := 1;
   Version_Minor : constant := 0;
   Version_Patch : constant := 0;

   --  Build mode identifiers
   type Build_Mode is (Debug, Release, Verify);

end Teras;
