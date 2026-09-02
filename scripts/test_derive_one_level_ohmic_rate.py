#!/usr/bin/env python3
from __future__ import annotations

import json
import math
import tempfile
import unittest
from pathlib import Path

from derive_one_level_ohmic_rate import (
    DerivationError,
    FORMULA_ID,
    LEAN_THEOREM,
    UNIT_CONTRACT,
    derive_rate,
)


class OhmicRateDerivationTests(unittest.TestCase):
    def make_source(self, root: Path, *, cutoff: float = 2.0) -> Path:
        gamma = 0.4
        shape_sum = 4.0
        coupling_sq = gamma * 4.0 * cutoff**3 / (math.pi * shape_sum)
        source = root / "ohmic-calibration-source.json"
        source.write_text(
            json.dumps(
                {
                    "schema_version": "1.0",
                    "calibration_id": "test-ohmic-rate",
                    "ohmic_coupling": {
                        "observable": "finite_ohmic_coupling",
                        "formula_id": FORMULA_ID,
                        "unit_contract": UNIT_CONTRACT,
                        "coupling_strength_sq": coupling_sq,
                        "cutoff": cutoff,
                        "shape_sum": shape_sum,
                        "rate_unit": "s^-1",
                    },
                    "equilibrium": {
                        "method": "fermi_dirac_beta_gap",
                        "beta_energy_gap": math.log(3.0),
                        "expected_occupation": 0.25,
                    },
                    "initial_condition": {"occupation": 0.9},
                    "source_observation_ids": ["coupling-fit", "bath-spectrum"],
                    "independent_of_target": True,
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        return source

    def test_derives_standard_calibration(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = self.make_source(root)
            summary = derive_rate(source, root / "out")
            self.assertAlmostEqual(summary["gamma"], 0.4, places=14)
            calibration = json.loads((root / "out/calibration.json").read_text())
            self.assertEqual(
                calibration["linewidth"]["observable"],
                "lorentzian_half_width",
            )
            self.assertAlmostEqual(calibration["linewidth"]["value"], 0.4, places=14)
            ids = calibration["source_observation_ids"]
            self.assertTrue(
                any(item.startswith("derived-rate-source-sha256:") for item in ids)
            )
            self.assertIn(f"derived-rate-theorem:{LEAN_THEOREM}", ids)
            derivation = json.loads(
                (root / "out/ohmic-rate-derivation.json").read_text()
            )
            self.assertEqual(derivation["formula_id"], FORMULA_ID)
            self.assertEqual(
                derivation["physical_bridge"]["status"], "conditional-model"
            )
            self.assertFalse(derivation["registry_mutation_performed"])

    def test_output_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = self.make_source(root)
            first = derive_rate(source, root / "out-1")
            second = derive_rate(source, root / "out-2")
            self.assertEqual(
                first["calibration_digest"], second["calibration_digest"]
            )
            self.assertEqual(first["derivation_digest"], second["derivation_digest"])

    def test_nonpositive_cutoff_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = self.make_source(root)
            payload = json.loads(source.read_text())
            payload["ohmic_coupling"]["cutoff"] = 0.0
            source.write_text(json.dumps(payload, sort_keys=True) + "\n")
            with self.assertRaisesRegex(DerivationError, "cutoff must be positive"):
                derive_rate(source, root / "out")

    def test_wrong_formula_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = self.make_source(root)
            payload = json.loads(source.read_text())
            payload["ohmic_coupling"]["formula_id"] = "unreviewed-formula"
            source.write_text(json.dumps(payload, sort_keys=True) + "\n")
            with self.assertRaisesRegex(DerivationError, "formula_id"):
                derive_rate(source, root / "out")


if __name__ == "__main__":
    unittest.main()
