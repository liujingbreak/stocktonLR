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

gulp.task('default', function() {
    console.log('gulp task [default] ...')
});

gulp.task('jshint', function() {

});

gulp.task('watch', function () {
    var watcher = gulp.watch(SRC, []);
    watcher.on('change', function (event) {
        console.log('File ' + event.path + ' was ' + event.type + ', running tasks...');
    });
});
gulp.task('clear', function (done) {
    cache.clearAll(function() {
        del(['build'], done);
    });

});