docker run --rm \
     --volume="$PWD:/srv/jekyll:Z" \
     --volume="$PWD/vendor/bundle:/usr/local/bundle:Z" \
     --publish [::1]:4000:4000 \
     jekyll/jekyll \
     jekyll serve \
     --force_polling
