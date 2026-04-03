import {
  RouterUtils,
  screenSize as getScreenSize,
  ScreenMode,
  ScreenUtils,
  PlatformUtils,
  t,
} from '@hw-vmall/vrn-basic-comp';
import React, { Component } from 'react';
import { Modal, View, Text, TouchableOpacity } from 'react-native';
import { WebView } from 'react-native-webview';
import { DialogType } from '../../../../types/commonType';

class BirthdayGift extends Component<any, any> {
  gotoPageTimer: any = null; // IOS规避modal中链接无法跳转
  webviewRef: any = null;
  injectTimer: any = null;
  constructor(props) {
    super(props);
    this.state = {
      modalVisible: true,
      birthdayModalVisible: true,
      opacity: 0,
    };
  }

  componentDidMount() {}

  componentWillUnmount() {
    clearTimeout(this.injectTimer);
  }

  isPadHorizontal = () => {
    return ScreenUtils.isPadHorizontal(ScreenMode.width, ScreenMode.height);
  };

  onMessage = async (event) => {
    const { env } = this.props;
    const action = JSON.parse(event.nativeEvent.data);
    if (action.type === 'closeDialog') {
      this.setState({ modalVisible: false }, () => {
        this.props.changeDialog();
      });
    } else if ((action.type = 'sureBtn')) {
      const url = `${env.wapDomain}upgradeGift`;
      this.setState({ modalVisible: false }, () => {
        this.props.changeDialog();
      });
      this._gotoPage(url);
    }
  };

  // IOS modal链接直接跳转失败，通过添加时延规避，待modal关闭后在跳转
  _gotoPage = (url: any) => {
    if (PlatformUtils.isIOS()) {
      this.gotoPageTimer && clearTimeout(this.gotoPageTimer);
      this.gotoPageTimer = setTimeout(() => {
        RouterUtils.gotoPage(url);
      }, 800);
    } else {
      RouterUtils.gotoPage(url);
    }
  };

  handleLoad = () => {
    const baseScript = `
    var birthClose = document.getElementsByClassName('birth-close')[0];
    var pickupBtn = document.getElementsByClassName('birth-btn')[0];
    birthClose.addEventListener('click', function() {
      window.ReactNativeWebView.postMessage(JSON.stringify({
        type: 'closeDialog'
      }))
    })
    pickupBtn.addEventListener('click', function() {
      window.ReactNativeWebView.postMessage(JSON.stringify({
        type: 'sureBtn'
      }))
    })
    `;
    clearTimeout(this.injectTimer);
    this.injectTimer = setTimeout(() => {
      this.webviewRef?.injectJavaScript(baseScript);
    }, 500);
  };

  isPad = () => {
    return getScreenSize(ScreenMode.width) === 'medium';
  };

  // 生日弹框-点放弃按钮
  closeBirthModal = () => {
    this.setState({
      birthdayModalVisible: false,
    }, () => {
      this.props.changeDialog();
    })
  }
  // 生日弹窗-点击去领取按钮
  clickReceiveBtn = () => {
    const { env } = this.props;
    const url = `${env.wapDomain}member/birthday/privileges`;
    this.setState({ birthdayModalVisible: false }, () => {
      this.props.changeDialog();
    });
    this._gotoPage(url);
  }
  // 生日礼包弹窗
  renderBirthdayModal() {
    const { styles, point } = this.props;
    const { birthdayModalVisible } = this.state;
    const modalWidth = this.isPad() ? 400 : 328;
    const buttonWidth = this.isPad() ? 170 : 140;
    const lineMargin = this.isPad() ? 10 : 8;
    return (
      <Modal
        animationType="fade"
        transparent={true}
        visible={birthdayModalVisible}
        presentationStyle="overFullScreen"
        statusBarTranslucent={true}>
        <View style={[styles.birthModalLayer,{ opacity: this.state.opacity }]} onLayout={() => {
          this.setState({ opacity: 1 })
        }}>
          <View style={[styles.birthModalBox, { width: modalWidth }]}>
            <View>
              <Text style={styles.birthTitle}>{t('birthTitle')}</Text>
              <Text
                style={styles.birthSubTitle}
              >
                {t('birthSubTitle').replace('%d', point)}
              </Text>
              <Text
                style={styles.birthTips}
              >
                {t('birthTips')}
              </Text>
            </View>
            <View
              style={styles.birthBtnContainer}
            >
              <TouchableOpacity onPress={this.closeBirthModal} style={[
                styles.birthBtn,
                {
                  width: buttonWidth,
                },
              ]}>
                <Text
                  style={[styles.commonTxt, styles.giveUpTxt]}
                >
                  {t('giveUp')}
                </Text>
              </TouchableOpacity>
              <View
                style={[
                  styles.line,
                  {
                    marginLeft: lineMargin,
                    marginRight: lineMargin,
                  },
                ]}
              />
              <TouchableOpacity onPress={this.clickReceiveBtn} style={[
                styles.birthBtn,
                styles.receiveBtn,
                {
                  width: buttonWidth,
                },
              ]}>
                <Text
                  style={[styles.commonTxt, styles.receiveTxt]}
                >
                  {t('goGetIt')}
                </Text>
              </TouchableOpacity>
            </View>
          </View>
        </View>
      </Modal>
    );
  }

  // 升级礼包弹窗
  renderUpgradeModal() {
    const { content, point } = this.props;
    let baseContent = content?.replace(/%%/g, '%').replace(/%s/, point);
    if (this.isPad()) {
      if (this.isPadHorizontal()) {
        baseContent = baseContent?.replace(/100vw/g, '30vw');
      } else {
        baseContent = baseContent?.replace(/100vw/g, '50vw');
      }
    }
    return this.state.modalVisible && baseContent ? (
      <Modal
        transparent={true}
        visible={this.state.modalVisible}
        presentationStyle="overFullScreen"
        statusBarTranslucent={true}
      >
        <WebView
          style={{
            backgroundColor: 'transparent',
          }}
          ref={(ref) => {
            this.webviewRef = ref;
          }}
          javaScriptEnabled={true}
          decelerationRate="normal"
          scalesPageToFit={false}
          originWhitelist={['*']}
          source={{ html: baseContent, baseUrl: '' }}
          bounces={false}
          scrollEnabled={false}
          textZoom={100} // 适配安卓字体变化
          contentInset={{ top: 0, left: 0 }}
          onMessage={(event) => this.onMessage(event)}
          onLoadEnd={() => this.handleLoad()}
        />
      </Modal>
    ) : null;
  }

  render() {
    const { type } = this.props;
    switch (type) {
      case DialogType.POP_UP_UPGRADE_MODAL:
        return this.renderUpgradeModal();
      case DialogType.POP_UP_BIRTHDAY_MODAL:
        return this.renderBirthdayModal();
      default:
        return null;
    }
  }
}
export default BirthdayGift;
