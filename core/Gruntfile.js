
module.exports = function(grunt) {

grunt.initConfig({
  jasmine_node: {
    options: {
      forceExit: true,
      match: '.',
      matchall: false,
      extensions: 'js',
      specNameMatcher: 'spec',
      jUnit: {
        report: true,
        savePath : "./build/jasmine/",
        useDotNotation: true,
        consolidate: true
      }
    },
    all: ['test/']
  }
});

grunt.loadNpmTasks('grunt-jasmine-node');

grunt.registerTask('default', ['jasmine_node']);

};
