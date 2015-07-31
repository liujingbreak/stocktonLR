var path = require('path');
var runner = require(path.join(__dirname,'node_modules/jasmine-node/lib/jasmine-node/runner.js'));

if (require.main === module) {
    if( !process.env.NODE_ENV ) process.env.NODE_ENV = 'test';

    var options = runner.parseArgs();
    runner.runSpecs(options);
} else {
    exports.runner = runner;
}