# Find and remove all 'target' directories
find . -name "target" -type d -exec rm -rf {} +

echo "All target directories have been removed."