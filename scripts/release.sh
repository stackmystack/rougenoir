#!/usr/bin/env bash

set -e

version=${1:-"v$(git cliff --bumped-version)"}

echo "Preparing $version..."
# lint and test first
just lint
just test
# update the version
msg="# managed by release.sh"
sed -E -i "s/^version = .*\s+$msg$/version = \"${version#v}\" $msg/" Cargo.toml
# update the changelog
git cliff --unreleased --tag "$version" --prepend CHANGELOG.md
git add -A && git commit -m "chore(release): $version"
git show
# generate a changelog for the tag message
export GIT_CLIFF_TEMPLATE="\
	{% for group, commits in commits | group_by(attribute=\"group\") %}
	{{ group | upper_first }}\
	{% for commit in commits %}
		- {% if commit.breaking %}(breaking) {% endif %}{{ commit.message | upper_first }} ({{ commit.id | truncate(length=7, end=\"\") }})\
	{% endfor %}
	{% endfor %}"
changelog=$(git cliff --unreleased --strip all)
# create a tag
git tag -a "$version" -m "Release $version" -m "$changelog"
echo "Done!"
echo "Now push the commit (git push origin master) and the tag (git push origin refs/tags/$version)."

