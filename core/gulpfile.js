var gulp = require('gulp'),
    //autoprefixer = require('gulp-autoprefixer'),
    //minifycss = require('gulp-minify-css'),
    jshint = require('gulp-jshint'),
    changed = require('gulp-changed');
    //uglify = require('gulp-uglify'),
    //imagemin = require('gulp-imagemin'),
    //rename = require('gulp-rename'),
    //concat = require('gulp-concat'),
    //notify = require('gulp-notify'),
    cache = require('gulp-cache'),
    //livereload = require('gulp-livereload'),
    del = require('del');

var SRC = 'src/**/*.js';
var jshintSrc = SRC;

gulp.task('default', function() {
    console.log('+ gulp task [default] ...')
});

gulp.task('jshint', function() {
    console.log('jshint on '+ jshintSrc);
    gulp.src(jshintSrc).pipe(jshint())
        .pipe(jshint.reporter('jshint-stylish'));
});

gulp.task('watch', function () {
    var watcher = gulp.watch(SRC, ['jshint']);
    watcher.on('change', function (event) {
        console.log('File ' + event.path + ' was ' + event.type + ', running tasks...');
        jshintSrc = event.path;
    });
});
gulp.task('clear', function (done) {
    cache.clearAll(function() {
        del(['build'], done);
    });

});