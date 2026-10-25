@echo off
cd /d "%~dp0"
py -3 cpm_pert.py
if errorlevel 1 python cpm_pert.py
if errorlevel 1 pause
