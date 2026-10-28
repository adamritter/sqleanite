#!/usr/bin/env python3
"""Continuing Core API observations of actual PK reseek after BEFORE programs."""
import unittest
from test_without_rowid_reseek import BASE,AFTER,Q
from test_error_effects import case
class WithoutRowidReseekEffects(unittest.TestCase):pass
for name,sql in Q.items():setattr(WithoutRowidReseekEffects,'test_'+name,case(BASE+sql+AFTER))
if __name__=='__main__':unittest.main()
